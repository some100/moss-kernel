use std::{
    ptr,
    sync::atomic::{AtomicBool, Ordering},
};
static SIGNAL_CAUGHT: AtomicBool = AtomicBool::new(false);

extern "C" fn signal_handler(_: libc::c_int) {
    SIGNAL_CAUGHT.store(true, Ordering::Relaxed);
}

fn register_handler(signum: libc::c_int, restart: bool) {
    unsafe {
        SIGNAL_CAUGHT.store(false, Ordering::Relaxed);
        let mut action: libc::sigaction = std::mem::zeroed();

        action.sa_sigaction = signal_handler as *const () as usize;

        action.sa_flags = if restart { libc::SA_RESTART } else { 0 };

        libc::sigemptyset(&mut action.sa_mask);

        if libc::sigaction(signum, &action, std::ptr::null_mut()) != 0 {
            panic!("Failed to register signal handler");
        }
    }
}

pub fn test_interruptible_nanosleep() {
    print!("Testing interruptible nanosleep (EINTR) ...");

    register_handler(libc::SIGALRM, false);

    unsafe {
        let pid = libc::getpid();

        if libc::fork() == 0 {
            // in child.
            let req = libc::timespec {
                tv_sec: 1,
                tv_nsec: 0,
            };

            libc::nanosleep(&req, ptr::null_mut());
            libc::kill(pid, libc::SIGALRM);
            libc::exit(0);
        };

        // Sleep for 5 seconds (much longer than the alarm)
        let req = libc::timespec {
            tv_sec: 5,
            tv_nsec: 0,
        };
        let mut rem = libc::timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };

        let ret = libc::nanosleep(&req, &mut rem);
        let err = std::io::Error::last_os_error();

        // Nanosleep should return -1
        assert_eq!(ret, -1);

        // Errno should be EINTR
        assert_eq!(err.raw_os_error(), Some(libc::EINTR));

        // The signal handler should have run
        assert!(SIGNAL_CAUGHT.load(Ordering::Relaxed));

        // The remaining time should be updated (approx 4 seconds left)
        assert!(rem.tv_sec >= 3 && rem.tv_sec <= 5);
    }
    println!(" OK");
}
