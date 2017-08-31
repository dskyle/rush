use interp::Interp;
use rush_pat::range::Range;
use rush_rt::range::RangeExt;
//use std::process::Command;
use rush_rt::val::{Val, ValIterOps, InternalIterable};
use self::Val::*;
use std::borrow::{Cow};
use jobs::Jobs;
use nix::libc::pid_t;
use nix::sys::wait::WaitStatus;
use jobs::Job;

pub fn add(val: &Val) -> i64 {
    let mut acc = 0;
    Cow::from(val).for_each(&mut |s: Cow<str>, _| { acc += str::parse::<i64>(&*s).unwrap_or(0); return true } );
    acc
}

pub fn echo(val: &Val) {
    let mut count = 0;
    Cow::from(val).for_each(&mut |s: Cow<str>, _| {
        if count > 0 { print!(" "); }
        print!("{}", &*s);
        count += 1;
        return true
    });
    println!("");
}

pub fn repr(val: &Val) -> String {
    if val.len() == 1 {
        val.iter().next().unwrap().repr()
    } else {
        val.repr()
    }
}

pub fn len(val: &Val) -> String {
    if val.len() == 1 {
        val.iter().next().unwrap().len()
    } else {
        val.len()
    }.to_string()
}

pub fn count(val: &Val) -> String {
    if val.len() == 1 {
        val.iter().next().unwrap().count()
    } else {
        val.count()
    }.to_string()
}

pub fn debug(val: &Val) {
    if val.len() == 1 {
        println!("{:?}", val.iter().next().unwrap());
    } else {
        println!("{:?}", val);
    }
}

fn job2val(job: ::jobs::Job) -> Val {
    use self::Job::*;
    use self::WaitStatus::*;
    match job {
        Foreground(_, _, status) => {
            match status {
                Some(Exited(_, code)) => {
                    Tup(vec![Str("Status".into()), Str(code.to_string())])
                },
                Some(Signaled(_, sig, _)) => {
                    Tup(vec![Str("Killed".into()), Str(format!("{:?}", sig))])
                },
                _ => unreachable!(),
            }
        },
        Background(pid, jid, status) => {
            Tup(vec![Str("Suspended".into()), Str(jid.to_string()),
                     Tup(vec![Val::str("Pid"), Str(i32::from(pid).to_string())])])
        },
        _ => unreachable!(),
    }
}

pub fn system(interp: &mut Interp, val: &Val) -> Val {
    use ::std::iter::IntoIterator;

    let cmd = val.iter().flatten();
    let mut iter = cmd.take_tup().unwrap().into_iter().map(|x| x.take_str().unwrap());
    interp.jobs.exec_fg(iter.collect()).map(|x| job2val(x)).unwrap_or(Val::err_str("bad exec"))
    /*
    let status = Command::new(iter.next().expect("system requires at least one argument")).args(iter).status();
    match status {
        Ok(status) => {
            match status.code() {
                Some(i) => Tup(vec![Str("Status".into()), Str(i.to_string())]),
                None => Tup(vec![Str("Killed".into()), Str("Unknown".into())]),
            }
        },
        Err(error) => {
            Val::err_string(format!("Error calling {:?}: {}", val, error))
        },
    }*/
}

pub fn equals(l: &Val, r: &Val) -> Val {
    //println!("equals: {:?}  {:?}", l, r);
    let eq = Cow::from(l).for_each_pairs(r, &mut |l: Option<Cow<str>>, r: Option<&str>, _| {
        //println!("{}: {:?} ?= {:?}", d, l, r);
        match (l, r) {
            (Some(l), Some(r)) => { return l.as_ref() == r; },
            _ => return false,
        }
    });
    if eq {
        Val::true_()
    } else {
        Val::false_()
    }
}

pub fn range_iter_start(l: &Val, r: &Val) -> Val {
    let range = Range::from_val_pair(l, r).unwrap();
    Val::Tup(vec![Val::str("Range::Iter"), range.first().unwrap(), l.clone(), r.clone()])
}

pub fn range_iter_next(cur: &Val, l: &Val, r: &Val) -> Val {
    let range = Range::from_val_pair(l, r).unwrap();
    let next = range.next(cur).unwrap();
    let len = { next.get_tup().map(|x| x.len()).unwrap_or(1) };
    if len == 0 {
        Val::void()
    } else {
        Val::Tup(vec![Val::str("Range::Iter"), next, l.clone(), r.clone()])
    }
}

pub fn get_home() -> String {
    use std::env::var;
    let home = var("HOME").unwrap_or_else(|_| {
        use users::{get_user_by_uid, get_current_uid};
        let user = get_user_by_uid(get_current_uid()).unwrap();
        let username = user.name();

        "/home/".to_string() + username
    });
    home
}

pub fn cd(mut dir: Cow<str>) -> Val {
    use std::env::{current_dir, set_current_dir};
    use std::path::{PathBuf};
    use std::sync::Mutex;
    use std::ops::{Deref, DerefMut};

    lazy_static! {
            static ref LAST_DIR: Mutex<String> = Mutex::new(get_home());
    }

    let old_dir = current_dir().unwrap_or_else(|_| { PathBuf::from("/") });
    if dir == "~" || dir.starts_with("~/") {
        dir = Cow::Owned(get_home() + &dir[1..]);
    }
    if dir == "-" {
        dir = Cow::Owned(LAST_DIR.lock().unwrap().deref().clone());
    }
    let mut new_dir = old_dir.clone();
    new_dir.push(dir.as_ref());
    if let Err(err) = set_current_dir(new_dir) {
        Val::err_string(format!("{}", err))
    } else {
        {
            *LAST_DIR.lock().unwrap().deref_mut() = old_dir.to_string_lossy().to_owned().into();
        }
        Val::void()
    }
}

pub fn jobs(j: &Jobs) -> Val {
    let jobs = j.iter().filter_map(|job| {
        if let Some(jid) = job.jid() {
            Some(Val::Tup(vec![Val::str("Job"),
                          Val::Str(jid.to_string()),
                          Val::Str(pid_t::from(job.pid().unwrap()).to_string()),
                          Val::Str(format!("{:?}", job.status()))]))
        } else {
            None
        }
    }).collect();
    Val::Tup(jobs)
}

pub fn fg(j: &mut Jobs, id: usize) -> Val {
    match j.fg(id) {
        Ok(job) => job2val(job),
        Err(e) => Val::err_string(e),
    }
}

pub fn file2string(fname: &str) -> String {
    use std::fs::File;
    use std::io::BufReader;
    use std::io::Read;

    let file = File::open(fname).unwrap();
    let mut buf_reader = BufReader::new(file);
    let mut contents = String::new();
    buf_reader.read_to_string(&mut contents).unwrap();
    contents
}
