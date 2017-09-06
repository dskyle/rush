use std::collections::{HashMap};
use std::collections::{BTreeMap};
use sitter::Sitter;
use nix::Error;
use nix::unistd::Pid;
use nix::sys::wait::{WaitStatus};
use nix::sys::signal::{sigaction, SigSet, SigAction, SaFlags, SigHandler, Signal};
use nix::sys::signal::{SigmaskHow, pthread_sigmask};
use std::cell::{Cell, RefCell};
use nix::unistd::{fork, execvp, ForkResult, tcsetpgrp, getpgrp, setpgid, getpid};
use std::ffi::CString;
use std::sync::atomic::{AtomicI32, Ordering};
use std::os::unix::io::RawFd;
use nix::fcntl::{open, self};
use nix::sys::stat;

trait PostInc {
    fn post_inc(&mut self) -> Self;
}

impl PostInc for usize {
    fn post_inc(&mut self) -> usize {
        let ret = *self;
        *self += 1;
        ret
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Job {
    Foreground(Pid, Option<usize>, Option<WaitStatus>),
    Background(Pid, usize, Option<WaitStatus>),
    Unknown(Pid, WaitStatus),
}

impl Job {
    pub fn pid(&self) -> Option<Pid> {
        use self::Job::*;

        match *self {
            Foreground(pid, ..) | Background(pid, ..) | Unknown(pid, ..)=> Some(pid),
        }
    }

    pub fn jid(&self) -> Option<usize> {
        use self::Job::*;

        match *self {
            Foreground(_, jid, ..) => jid,
            Background(_, jid, ..) => Some(jid),
            _ => None,
        }
    }

    pub fn status(&self) -> Option<WaitStatus> {
        use self::Job::*;

        match *self {
            Foreground(_, _, status, ..) | Background(_, _, status, ..) => status,
            _ => None,
        }
    }

    pub fn set_status(&mut self, new_status: Option<WaitStatus>) {
        use self::Job::*;

        match *self {
            Foreground(_, _, ref mut status, ..) | Background(_, _, ref mut status, ..) => *status = new_status,
            _ => {},
        };
    }
}

fn get_pid(status: &WaitStatus) -> Option<Pid> {
    use self::WaitStatus::*;

    match *status {
        Exited(pid, ..) | Signaled(pid, ..) | Stopped(pid, ..) |
        PtraceEvent(pid, ..) | PtraceSyscall(pid, ..) |
        Continued(pid, ..) => Some(pid),
        StillAlive => None,
    }
}

pub type JobMap = HashMap<Pid, (Job, Cell<bool>)>;

pub static FG_PID: AtomicI32 = AtomicI32::new(0);
pub struct Jobs {
    jobs: JobMap,
    ids: BTreeMap<usize, Pid>,
    cur_id: usize,
    fg_pid: Option<Pid>,
    unknown_jobs: RefCell<Vec<Job>>,
    tty_fd: RawFd,

    sitter: Sitter,

    oldint: SigAction,
    oldtstp: SigAction,
    oldquit: SigAction,
    oldttou: SigAction,
}

impl Drop for Jobs {
    fn drop(&mut self) {
        unsafe { sigaction(Signal::SIGINT, &self.oldint).unwrap() };
        unsafe { sigaction(Signal::SIGTSTP, &self.oldtstp).unwrap() };
        unsafe { sigaction(Signal::SIGQUIT, &self.oldquit).unwrap() };
        unsafe { sigaction(Signal::SIGTTOU, &self.oldttou).unwrap() };
    }
}

extern "C" fn forward_handler(sig: ::nix::libc::c_int) {
    let pid = ::jobs::FG_PID.load(Ordering::SeqCst);
    if pid > 0 {
        ::nix::unistd::write(0, "forwarding signal\n".as_bytes()).unwrap();
        ::nix::sys::signal::kill(Pid::from_raw(pid), Some(Signal::from_c_int(sig).unwrap())).unwrap();
    }
}

const JOBS_CAPACITY: usize = 1024;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SpawnResult {
    Original(Job),
    Child,
}

/*
fn reset_signals() {
    sigaction(Signal::SIGCHLD, &SigAction::new(SigHandler::SigDfl, SaFlags::empty(), SigSet::empty())).unwrap()
}*/

fn unblock_all_signals() -> Result<(), Error> {
    pthread_sigmask(SigmaskHow::SIG_SETMASK, Some(&SigSet::empty()), None)
}

impl Jobs {
    pub fn new() -> Jobs {
        FG_PID.store(0, Ordering::SeqCst);
        let action = SigAction::new(SigHandler::Handler(forward_handler), SaFlags::empty(), SigSet::all());
        let ignore = SigAction::new(SigHandler::SigIgn, SaFlags::empty(), SigSet::all());

        Jobs {
            jobs: JobMap::new(),
            cur_id: 0,
            ids: BTreeMap::new(),
            fg_pid: None,
            unknown_jobs: RefCell::new(Vec::new()),
            tty_fd: open("/dev/tty", fcntl::O_RDWR | fcntl::O_NONBLOCK, stat::Mode::empty()).unwrap(),

            sitter: Sitter::with_capacity(JOBS_CAPACITY),

            oldint: unsafe { sigaction(Signal::SIGINT, &action).unwrap() },
            oldtstp: unsafe { sigaction(Signal::SIGTSTP, &action).unwrap() },
            oldquit: unsafe { sigaction(Signal::SIGQUIT, &action).unwrap() },
            oldttou: unsafe { sigaction(Signal::SIGTTOU, &ignore).unwrap() },
        }
    }

    pub fn add_bg(&mut self, pid: Pid) -> Job {
        let id = self.cur_id.post_inc();
        let job = Job::Background(pid, id, None);
        self.jobs.insert(pid, (job, Cell::new(false)));
        self.ids.insert(id, pid);
        job
    }

    pub fn add_fg(&mut self, pid: Pid) -> Job {
        assert!(self.fg_pid == None, "Tried to start fg job when one already exists");
        let job = Job::Foreground(pid, None, None);
        self.jobs.insert(pid, (job, Cell::new(false)));
        job
    }

    fn init_child(&self) {
        unblock_all_signals().unwrap();
        setpgid(Pid::from_raw(0), getpid()).unwrap();
    }

    pub fn spawn_bg(&mut self) -> Result<SpawnResult, Error> {
        match fork() {
            Ok(ForkResult::Parent { child, .. }) => {
                let job = self.add_bg(child.into());
                Ok(SpawnResult::Original(job))
            },
            Ok(ForkResult::Child) => {
                self.init_child();
                Ok(SpawnResult::Child)
            },
            Err(e) => Err(e),
        }
    }

    pub fn get_fg_pid(&self) -> Option<Pid> {
        return self.fg_pid;
    }

    fn set_fg_pid(&mut self, pid: Option<Pid>) {
        self.fg_pid = pid;
        FG_PID.store(pid.map(|x| i32::from(x)).unwrap_or(0), Ordering::SeqCst);
    }

    pub fn fg(&mut self, id: usize) -> Result<Job, String> {
        if let Some(pid) = self.ids.remove(&id) {
            if let Some(&mut (ref mut job, ref mut dirty)) = self.jobs.get_mut(&pid) {
                match *job {
                    Job::Foreground(_, _, _) => {
                    },
                    Job::Background(_, jid, _) => {
                        *job = Job::Foreground(pid, Some(jid), None);
                        dirty.set(false);
                    },
                    _ => unreachable!(),
                }
            } else { return Err("Unknown pid".into()); }
            use nix::sys::signal;
            signal::kill(pid, Some(signal::Signal::SIGCONT)).unwrap();
            return Ok(self.watch(pid).unwrap());
        } else { return Err("Unknown job id".into()); }
    }

    pub fn bg(&mut self, id: usize) -> Result<Job, String> {
        if let Some(pid) = self.ids.remove(&id) {
            if let Some(&mut (ref mut job, ref mut dirty)) = self.jobs.get_mut(&pid) {
                match *job {
                    Job::Foreground(_, _, _) => {
                        let jid = if let Some(jid) = job.jid() { jid } else { self.cur_id.post_inc() };
                        *job = Job::Background(pid, jid, None);
                        dirty.set(false);
                    },
                    Job::Background(_, _, ref mut cur_status) => {
                        *cur_status = None;
                    },
                    _ => unreachable!(),
                }
            } else { return Err("Unknown pid".into()); }
            use nix::sys::signal;
            signal::kill(pid, Some(signal::Signal::SIGCONT)).unwrap();
            return Ok(self.watch(pid).unwrap());
        } else { return Err("Unknown job id".into()); }
    }

    fn watch(&mut self, pid: Pid) -> Result<Job, Error> {
        self.set_fg_pid(Some(pid));
        tcsetpgrp(self.tty_fd, pid).unwrap();
        let ret = loop {
            self.poll();
            let (ref mut job, _) = *self.jobs.get_mut(&pid).expect("Watched job disappeared!");
            use self::WaitStatus::*;
            let status = job.status();
            match status {
                None | Some(StillAlive) => {},
                Some(Exited(..)) | Some(Signaled(..)) => {
                    job.set_status(status);
                    break Ok(*job);
                },
                Some(Stopped(pid, ..)) | Some(PtraceEvent(pid, ..)) | Some(PtraceSyscall(pid, ..)) => {
                    let jid = if let Some(jid) = job.jid() { jid } else { self.cur_id.post_inc() };
                    *job = Job::Background(pid, jid, status);
                    self.ids.insert(jid, pid);
                    break Ok(*job);
                },
                Some(Continued(..)) => {
                    job.set_status(status);
                },
            }
            let _ = ::nix::unistd::pause();
        };
        tcsetpgrp(self.tty_fd, getpgrp()).unwrap();
        self.set_fg_pid(None);
        ret
    }

    pub fn exec_fg(&mut self, cmd: Vec<String>) -> Result<Job, Error> {
        match fork() {
            Ok(ForkResult::Parent{child, ..}) => {
                let job = self.add_fg(child.into());
                self.watch(job.pid().unwrap())
            },
            Ok(ForkResult::Child) => {
                let i = cmd.into_iter().filter_map(|x| CString::new(x.into_bytes()).ok());
                let args: Vec<_> = i.collect();
                let name = &args[0];
                self.init_child();
                match execvp(name, &args[..]) {
                    Ok(..) => unreachable!(),
                    Err(e) => eprintln!("exec error: {:?}", e),
                }
                ::std::process::exit(255);
            },
            Err(e) => Err(e),
        }
    }

    pub fn iter(&self) -> Iter {
        Iter{jobs: self, iter: self.ids.iter()}
    }

    pub fn poll(&mut self) {
        for status in self.sitter.iter() {
            if let Some(pid) = get_pid(&status) {
                if let Some(&mut (ref mut job, ref mut dirty)) = self.jobs.get_mut(&pid) {
                    match *job {
                        Job::Foreground(_, _, ref mut cur_status) => *cur_status = Some(status),
                        Job::Background(_, _, ref mut cur_status) => *cur_status = Some(status),
                        _ => unimplemented!(),
                    }
                    dirty.set(true);
                } else {
                    self.unknown_jobs.borrow_mut().push(Job::Unknown(pid, status));
                }
            }
        }
    }

    pub fn check(&self) -> Vec<Job> {
        let mut ret = vec![];
        for (_, &(ref job, ref dirty)) in self.jobs.iter() {
            if dirty.take() {
                ret.push(*job);
            }
        }
        ret.append(&mut *self.unknown_jobs.borrow_mut());
        return ret;
    }
}

pub struct Iter<'a> {
    jobs: &'a Jobs,
    iter: ::std::collections::btree_map::Iter<'a, usize, Pid>,
}

impl<'a> Iterator for Iter<'a>{
    type Item = Job;

    fn next(&mut self) -> Option<Job> {
        loop {
            if let Some((_, pid)) = self.iter.next() {
                if let Some(j) = self.jobs.jobs.get(pid) {
                    return Some(j.0);
                }
            } else {
                return None;
            }
        }
    }
}
