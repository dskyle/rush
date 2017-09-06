use rush_parser::ast::{ExprS};
use rush_rt::vars::{LocalVars};
use rush_rt::val::{Val};
use nix::unistd::{fork, ForkResult, pipe, dup, dup2, close};
use nix::sys::wait::{WaitStatus};
use interp::Interp;
use func::Control;

#[derive(Debug)]
pub enum StageStatus {
    Initialized,
    Background(i32),
    Foreground,
    Completed(WaitStatus),
}

#[derive(Debug)]
pub struct Stage<'a> {
    code: &'a ExprS,
    status: StageStatus,
}

impl<'a> Stage<'a> {
    fn create(code: &'a ExprS) -> Stage {
        Stage{code, status: StageStatus::Initialized}
    }
}

#[derive(Debug)]
pub struct Pipeline<'a> {
    stages: Vec<Stage<'a>>,
}

impl<'a> Pipeline<'a> {
    pub fn create(stages: &'a Vec<ExprS>) -> Pipeline {
        Pipeline{ stages: stages.into_iter().map(|x| Stage::create(x)).collect() }
    }

    pub fn exec(&mut self, interp: &mut Interp, local_vars: &mut LocalVars) -> (Val, Control) {
        let mut use_input = 0;
        let n = self.stages.len();
        if n == 0 {
            return (Val::void(), Control::Done);
        }
        for ref mut s in self.stages.iter_mut().take(n - 1) {
            let (pread, pwrite) = pipe().unwrap();
            let (input, output) = (use_input, pwrite);
            use_input = pread;
            match fork() {
                Ok(ForkResult::Parent { child, .. }) => {
                    s.status = StageStatus::Background(child.into());
                    if input != 0 {
                        close(input).unwrap();
                    }
                    if output != 1 {
                        close(output).unwrap();
                    }
                },
                Ok(ForkResult::Child) => {
                    if input != 0 {
                        dup2(input, 0).unwrap();
                        close(input).unwrap();
                    }
                    if output != 1 {
                        dup2(output, 1).unwrap();
                        close(output).unwrap();
                    }
                    let (val, _) = interp.exec_stmt(s.code, local_vars);
                    if let Val::Tup(ref v) = val {
                        if v.len() == 2 && v[0].get_str() == Some("Status") {
                            if let Some(v) = v[1].get_str() {
                                if let Ok(x) = str::parse::<i32>(v) {
                                    ::std::process::exit(x);
                                }
                            }
                        }
                    }
                    ::std::process::exit(0);
                },
                Err(_) => panic!("Fork failed!"),
            }
        }
        let (val, con) = {
            use nix::fcntl::{self, fcntl, FcntlArg};
            let last_stage = self.stages.last_mut().unwrap();

            let oldin = if use_input != 0 {
                let oldin = dup(0).unwrap();
                fcntl(oldin, FcntlArg::F_SETFL(fcntl::O_CLOEXEC)).unwrap();
                dup2(use_input, 0).unwrap();
                close(use_input).unwrap();
                Some(oldin)
            } else {
                None
            };

            last_stage.status = StageStatus::Foreground;
            let ret = interp.exec_stmt(last_stage.code, local_vars);

            if let Some(oldin) = oldin {
                dup2(oldin, 0).unwrap();
                close(oldin).unwrap();
            }

            ret
        };
        /*
        for ref mut s in self.stages.iter_mut() {
            if let StageStatus::Background(pid) = s.status {
                let status = waitpid(Some(Pid::from_raw(pid)), None).unwrap();
                s.status = StageStatus::Completed(status);
            }
        }*/
        return (val, con);
    }
}
