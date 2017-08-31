//! Sitter for handling child processes synchronously
//!
//! It works as follows:
//!
//! 1. You create a sitter (`Sitter::new()`), that is a RAII-style guard which
//!    takes over SIGCHLD handling while it exists; it restores any previous
//!    handling when it is dropped.
//!
//! 2. You ask latter, using poll(), what changes to children have happened
//!    since the last time poll() was called.

use std::ptr::null_mut;

use nix::sys::signal::{sigaction, SigAction, Signal, SigSet, SaFlags};
use nix::sys::signal::{SigHandler};
use nix::sys::wait::{self, waitpid, WaitStatus};
use libc;
use bounded_spsc_queue::{self, Consumer, Producer};
use std::sync::atomic::{AtomicPtr, Ordering};
use errno;

struct SitterImpl {
    qpro: Producer<WaitStatus>,
    qcon: Consumer<WaitStatus>,
}

/// Watches for SIGCHLD, and keeps a log of associated WaitStatuses. Use next()
/// to get the next logged WaitStatus. Iteration ends (returns None) if there
/// are none left.
pub struct Sitter {
    oldsig: SigAction,
    prev_sitter: *mut SitterImpl,

    imp: Box<SitterImpl>
}

static ACTIVE_SITTER: AtomicPtr<SitterImpl> = AtomicPtr::new(null_mut());
extern "C" fn sitter_handler(_: libc::c_int) {
    let last_errno = errno::errno();

    //::nix::unistd::write(2, "running handler\n".as_bytes());

    loop {
        let update = match waitpid(None, Some(wait::WNOHANG | wait::WCONTINUED | wait::WUNTRACED)) {
            Ok(WaitStatus::StillAlive) | Err(..) => break,
            Ok(status) => status,
        };
        if let Some(sitter) = unsafe { ACTIVE_SITTER.load(Ordering::SeqCst).as_ref() } {
            sitter.qpro.try_push(update);
        }
    }

    errno::set_errno(last_errno);
}

impl Sitter {
    /// Create and activate the signal trap for specified signals. Signals not
    /// in list will be delivered asynchronously as always.
    pub fn with_capacity(capacity: usize) -> Sitter {
        let mut sigset = SigSet::empty();
        sigset.add(Signal::SIGCHLD);
        let (qpro, qcon) = bounded_spsc_queue::make(capacity);
        let mut imp = Box::new(SitterImpl{qpro, qcon});
        let mut prev_sitter = &mut *imp as *mut SitterImpl;
        let oldsig = unsafe {
            prev_sitter = ACTIVE_SITTER.swap(prev_sitter, Ordering::SeqCst);

            sigaction(Signal::SIGCHLD,
                &SigAction::new(SigHandler::Handler(sitter_handler),
                    SaFlags::empty(), sigset)).unwrap()
        };

        Sitter {
            oldsig: oldsig,
            prev_sitter: prev_sitter,
            imp: imp,
        }
    }

    /// Get iterator for this Sitter
    pub fn iter(&self) -> SitterIter {
        SitterIter{sitter: self}
    }
}

/// Iterator for a Sitter
pub struct SitterIter<'a> {
    sitter: &'a Sitter,
}

impl<'a> Iterator for SitterIter<'a> {
    type Item = WaitStatus;
    fn next(&mut self) -> Option<WaitStatus> {
        self.sitter.imp.qcon.try_pop()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.sitter.imp.qcon.size(), Some(self.sitter.imp.qcon.capacity()))
    }
}

impl Drop for Sitter {
    fn drop(&mut self) {
        unsafe {
            ACTIVE_SITTER.swap(self.prev_sitter, Ordering::SeqCst);
            sigaction(Signal::SIGCHLD, &self.oldsig).unwrap();
        }
    }
}
