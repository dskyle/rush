extern crate rush;

extern crate rustyline;
extern crate linefeed;
extern crate hostname;
extern crate users;
extern crate ansi_term;

use rush::{util, Val, Processor};

fn make_prompt(color: bool, esc: bool) -> String {
    use users::{get_user_by_uid, get_current_uid};
    let user = get_user_by_uid(get_current_uid()).unwrap();
    let username = user.name();

    use hostname::get_hostname;
    let host = get_hostname().unwrap();

    use std::env;
    let path = env::current_dir().unwrap();

    if color {
        use ansi_term::Colour::{Red, Yellow, Blue};

        if esc {
            fn x(s: &str) -> String {
                let mut ret = String::with_capacity(s.len() + 2);
                ret.push('\x02');
                ret.push_str(&s);
                ret.push('\x01');
                ret
            }
            return format!("\x01{}\x02@\x01{}\x02 \x01{}\x02 $ ",
                           Blue.paint(x(username)),
                           Yellow.paint(x(&host)),
                           Red.bold().paint(x(&path.to_string_lossy())));
        } else {
            return format!("{}@{} {} $ ",
                           Blue.paint(username),
                           Yellow.paint(host),
                           Red.bold().paint(path.to_string_lossy()));
        }
    } else {
        return format!("{}@{} {} $ ",
                       username, host, path.to_string_lossy());
    }
}

fn do_interactive_command(processor: &mut Processor, line: &str) -> bool {
    use std::panic::{self, AssertUnwindSafe};

    let ret = panic::catch_unwind(AssertUnwindSafe(|| { processor.exec(&line) }));
    match ret {
        Ok((ret, con)) => {
            match ret {
                Val::Error(_) => {
                    println!("Error: {}", ret);
                },
                _ => {
                    println!(" => {}", ret.repr());
                },
            }
            if con.stops_exec() {
                return false;
            }
        },
        Err(_) => { },
    }
    true
}

fn do_interactive_lf() {
    use std::fs::File;
    use std::io::{BufReader, BufRead, Write};
    use linefeed::{Reader, ReadResult};
    use linefeed::terminal::Signal;
    use std::rc::Rc;

    let mut reader = Reader::new(make_prompt(false, true)).unwrap();

    reader.set_completer(Rc::new(linefeed::complete::PathCompleter{}));
    reader.set_report_signal(Signal::Quit, true);
    reader.set_report_signal(Signal::Break, true);
    reader.set_report_signal(Signal::Interrupt, true);
    reader.set_ignore_signal(Signal::Suspend, true);
    reader.set_catch_signals(true);

    let mut history_path = ::std::path::PathBuf::from(util::get_home());
    history_path.push(".rush_history");
    //let history_path = "/home/dskyle/.rush_history";

    {
        if let Ok(hist) = File::open(history_path.clone()) {
            let hist = BufReader::new(hist);
            for line in hist.lines() {
                if let Ok(line) = line {
                    reader.add_history(line)
                }
            }
        }
    }

    let mut processor = Processor::new();
    loop {
        reader.set_prompt(&make_prompt(true, true));

        match reader.read_line() {
            Ok(ReadResult::Input(input)) => {
                if input.len() == 0 { continue }

                let diff = {
                    let last = reader.history().last().unwrap_or("");
                    last != input
                };
                if diff { reader.add_history(input.clone()) }

                if !do_interactive_command(&mut processor, &input) { break }
            },
            Ok(ReadResult::Signal(signal)) => {
                match signal {
                    Signal::Interrupt | Signal::Break => println!("^C"),
                    Signal::Quit => { println!("Killed"); break },
                    Signal::Suspend => {},
                }
            },
            Ok(ReadResult::Eof) => {
                println!("exit");
                break
            },
            x => { println!("Got {:?}", x); break },
        }
    }

    {
        let mut hist = File::create(history_path).unwrap();
        for cmd in reader.history() {
            writeln!(hist, "{}", cmd).unwrap();
        }
    }
}

fn do_interactive() {
    use rustyline::error::ReadlineError;
    use rustyline::Editor;

    let mut rl = Editor::<()>::new();
    rl.load_history("history.txt").err();
    let mut processor = Processor::new();
    loop {
        let prompt = make_prompt(true, false);
        let readline = rl.readline(&prompt);
        match readline {
            Ok(line) => {
                if line.len() == 0 { continue }

                rl.add_history_entry(&line);

                if !do_interactive_command(&mut processor, &line) { break }
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

fn do_string(contents: String, args: Vec<String>) {
    let mut processor = Processor::new();
    processor.add_local("_args", Val::Tup(args.into_iter().map(|a| { Val::Str(a) }).collect()));
    processor.exec(&contents);
}

fn do_stdin(args: Vec<String>) {
    use rush::util;

    let contents = util::file2string("/dev/fd/0");
    do_string(contents, args);
}

fn do_file(args: Vec<String>) {
    use rush::util;

    assert!(args.len() > 0, "do_file requires at least 1 argument");
    let contents = util::file2string(&args[0]);
    do_string(contents, args);
}

fn do_usage() {
    eprintln!("rush: Rust Shell

Usage: rush FLAGS [(FILE | COMMAND) [ARGS ...]]

Flags (all must appear prior to positional arguments):
  -c      Use first positional argument as direct rush code instead of file name

  --help  print this help message
  --      All subsequent arguments treated as positional, even known flags

Positional Arguments:
  FILE         a rush script file to execute
  COMMAND      rush code to execute (if -c argument is given)
  ARGS         list of arguments to make available within script via $_args
");
}

struct RushArgs {
    pub help: bool,
    pub use_rustyline: bool,
    pub exec_cmd: bool,
    pub from_stdin: bool,
}

impl RushArgs {
    fn new() -> RushArgs {
        RushArgs {
            help: false,
            use_rustyline: false,
            exec_cmd: false,
            from_stdin: false,
        }
    }

    fn parse<V: IntoIterator<Item=String>>(args: V) -> (RushArgs, Vec<String>) {
        let mut ret = RushArgs::new();
        let mut iter = args.into_iter().peekable();
        loop {
            let mut done = false;
            {
                let cur = if let Some(cur) = iter.peek() {
                    cur
                } else {
                    break
                };
                match cur.as_ref() {
                    "-c" => ret.exec_cmd = true,
                    "-s" => ret.from_stdin = true,
                    "--help" => ret.help = true,
                    "--use-rustyline" => ret.use_rustyline = true,
                    "-" | "--" => done = true,
                    x if x.starts_with("-") => {
                        eprintln!("Invalid argument: {}", x);
                        do_usage();
                        ::std::process::exit(1);
                    },
                    _ => break,
                }
            };
            iter.next();
            if done { break }
        }
        return (ret, iter.collect());
    }
}

fn main() {
    let mut args: Vec<_> = ::std::env::args().collect();
    let (args, remain) = RushArgs::parse(args.drain(1..));
    if args.help {
        do_usage();
        return;
    }
    if remain.len() > 0 {
        if args.from_stdin {
            do_stdin(remain);
        } else if args.exec_cmd {
            let mut i = remain.into_iter();
            let c = i.next().unwrap();
            let a = i.collect();
            do_string(c, a);
        } else {
            do_file(remain);
        }
    } else {
        if args.use_rustyline {
            do_interactive();
        } else {
            do_interactive_lf();
        }
    }
}
