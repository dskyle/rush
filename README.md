`rush` is a new command line shell inspired by, and implemented in, the Rust
programming language. It is still in early development. Focus so far has been
on the core language engine and novel features. Many of the normal, expected
features of shells, such as job control and tab completion, are not yet in
place. As such, production usage of `rush`
is not advisable, but feedback and contributions are welcome.

See the [Wiki](https://github.com/dskyle/rush/wiki) for reference documentation.

# Installation

Currently, `rush` is only distributed in source form, and must be compiled.
First, ensure you have the **nightly** version of
[Rust installed](https://www.rust-lang.org/en-US/install.html).

Once Rust is installed, clone the repo, e.g.:

    git clone https://github.com/dskyle/rush.git

Then enter the directory and run:

    cargo build --release
    cargo install

This will install `rush` to your local cargo bin directory. To install
system wide, simply copy the executable; e.g.:

    sudo cp target/release/rush /usr/local/bin/.

# Basic Usage

`rust` supports interactive usage, but is currently limited compared to
`bash`. In particular, tab-completion is not yet supported, all
statements must be input on one line, and the prompt template is hard-coded.

Basic usage of `rust` resembles traditional shell usage. The following are
essentially unchanged from `bash` usage:

* Processes launch with the name of the program, followed by arguments,
separated by whitespace; e.g., `grep needle haystack.txt`.
* Pipelining together processes with the `|` character; e.g.,
`ls -alh | grep .rush | wc`. Only redirection of stdout is currently supported.
* Output file redirection with the `>` character; e.g., `ls > out.txt`.
Input redirection is not yet supported; use `cat file.name |` instead.
* Running a command in the background, with the `&` character.
* Variable substitution with the `$` character. Variable assignment, however,
uses the `let` keyword, and supports Rust-like pattern matching; e.g.,
`let x, y, z = 1, 2, 3`
* File name expansion with `*` and `?` in unquoted strings; e.g., `ls *.rs`

# Invocation

Run `rust` without arguments to enter interactive usage. The first argument
given, if any, must be a script file. It will be executed, and all arguments,
including the script's name, will be made available within via the $_args
variable. For example:

    $ cat example.rush
    let sname arg1 arg2 = $_args
    echo Script: $sname
    echo First arg: $arg1
    echo Second arg: $arg2
    $ rush example.rush hello world
    Script: example.rush
    First arg: hello
    Second arg: world
