extern crate rush;

extern crate rustyline;
extern crate hostname;
extern crate users;
extern crate ansi_term;

use rush::{Val, Processor};

fn make_prompt() -> String {
    use users::{get_user_by_uid, get_current_uid};
    let user = get_user_by_uid(get_current_uid()).unwrap();
    let username = user.name();

    use hostname::get_hostname;
    let host = get_hostname().unwrap();

    use std::env;
    let path = env::current_dir().unwrap();

    use ansi_term::Colour::{Red, Yellow, Blue};

    return format!("{}@{} {} $ ",
                   Blue.paint(username),
                   Yellow.paint(host),
                   Red.bold().paint(path.to_string_lossy()));
}

fn do_interactive() {
    use rustyline::error::ReadlineError;
    use rustyline::Editor;

    let mut rl = Editor::<()>::new();
    rl.load_history("history.txt").err();
    let mut processor = Processor::new();
    loop {
        let prompt = make_prompt();
        let readline = rl.readline(&prompt);
        match readline {
            Ok(line) => {
                rl.add_history_entry(&line);

                use std::panic::{self, AssertUnwindSafe};

                let ret = panic::catch_unwind(AssertUnwindSafe(|| { processor.exec(&line) }));
                match ret {
                    Ok((ret, con)) => {
                        match ret {
                            Val::Error(_) => {
                                println!("Error: {}", ret);
                            },
                            _ => {
                                println!(" => {}", ret);
                            },
                        }
                        if con.stops_exec() {
                            break;
                        }
                    },
                    Err(_) => { },
                }
            },
            Err(ReadlineError::Interrupted) => {
                continue
            },
            Err(ReadlineError::Eof) => {
                break
            },
            Err(err) => {
                println!("Error: {:?}", err);
                break
            }
        }
    }
    rl.save_history("history.txt").unwrap();
}

fn do_file(args: Vec<String>) {
    use std::fs::File;
    use std::io::BufReader;
    use std::io::Read;

    assert!(args.len() > 0, "do_file requires at least 1 argument");
    let contents = {
        let fname = &args[0];
        let file = File::open(fname).unwrap();
        let mut buf_reader = BufReader::new(file);
        let mut contents = String::new();
        buf_reader.read_to_string(&mut contents).unwrap();
        contents
    };

    let mut processor = Processor::new();
    processor.add_local("_args", Val::Tup(args.into_iter().map(|a| { Val::Str(a) }).collect()));
    processor.exec(&contents);
}

fn do_usage() {
    println!("rush: Rust Shell

Usage: rush [FLAGS] [SCRIPT] [[ARGS] ...]

Flags (all must appear prior to SCRIPT):
  --help  print this help message

Arguments:
  SCRIPT       a rush script file to execute
  ARGS         list of arguments to make available within script via $_args
");
}

fn main() {
    let mut args: Vec<_> = ::std::env::args().collect();
    if args.len() > 1 {
        if args[1] == "--help" {
            do_usage();
        } else {
            let script_args = args.split_off(1);
            do_file(script_args);
        }
    } else {
        do_interactive();
    }
}
