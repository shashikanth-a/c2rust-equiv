//! Running commands with a timeout.

use std::fs::{self, File};
use std::io::{self, Write};
use std::path::Path;
use std::process::{Command, ExitStatus, Stdio};
use std::time::Duration;

use wait_timeout::ChildExt;

pub struct Finished {
    /// `None` if the command timed out and was killed.
    pub status: Option<ExitStatus>,
    /// Combined stdout and stderr.
    pub output: String,
}

impl Finished {
    pub fn success(&self) -> bool {
        self.status.is_some_and(|s| s.success())
    }
}

/// Run `cmd` with `stdin` as input, killing it and its children after `timeout`.
/// Output goes through `log` rather than a pipe, so large output can't block it.
pub fn run(
    mut cmd: Command,
    stdin: Option<&str>,
    timeout: Duration,
    log: &Path,
) -> io::Result<Finished> {
    let out = File::create(log)?;
    cmd.stdout(out.try_clone()?).stderr(out);
    cmd.stdin(if stdin.is_some() {
        Stdio::piped()
    } else {
        Stdio::null()
    });
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        cmd.process_group(0);
    }
    let mut child = cmd.spawn()?;
    if let Some(input) = stdin {
        // Dropping the handle closes the pipe.
        child.stdin.take().unwrap().write_all(input.as_bytes())?;
    }
    let status = match child.wait_timeout(timeout)? {
        Some(status) => Some(status),
        None => {
            kill_group(&mut child);
            child.wait()?;
            None
        }
    };
    let output = String::from_utf8_lossy(&fs::read(log)?).into_owned();
    Ok(Finished { status, output })
}

fn kill_group(child: &mut std::process::Child) {
    #[cfg(unix)]
    {
        let _ = Command::new("kill")
            .arg("-KILL")
            .arg(format!("-{}", child.id()))
            .status();
    }
    let _ = child.kill();
}
