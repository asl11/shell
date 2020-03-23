/*
 * COMP 321 Project 4: Shell
 *
 * This program implements a tiny shell with job control.
 *
 * Alex Li asl11
 */

#include <sys/types.h>
#include <sys/wait.h>

#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <signal.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

// You may assume that these constants are large enough.
#define MAXLINE      1024   // max line size
#define MAXARGS       128   // max args on a command line
#define MAXJOBS        16   // max jobs at any point in time
#define MAXJID   (1 << 16)  // max job ID

// The job states are:
#define UNDEF 0 // undefined
#define FG 1    // running in foreground
#define BG 2    // running in background
#define ST 3    // stopped

/*
 * The job state transitions and enabling actions are:
 *     FG -> ST  : ctrl-z
 *     ST -> FG  : fg command
 *     ST -> BG  : bg command
 *     BG -> FG  : fg command
 * At most one job can be in the FG state.
 */

struct Job {
	pid_t pid;              // job PID
	int jid;                // job ID [1, 2, ...]
	int state;              // UNDEF, FG, BG, or ST
	char cmdline[MAXLINE];  // command line
};

struct list {
	char *name;
	struct list *tail_list;
};

typedef volatile struct Job *JobP;

/*
 * Define the jobs list using the "volatile" qualifier because it is accessed
 * by a signal handler (as well as the main program).
 */
static volatile struct Job jobs[MAXJOBS];
static int nextjid = 1;            // next job ID to allocate

extern char **environ;             // defined by libc

static char prompt[] = "tsh> ";    // command line prompt (DO NOT CHANGE)
static bool verbose = false;       // If true, print additional output.

static struct list *paths;

/*
 * The following array can be used to map a signal number to its name.
 * This mapping is valid for x86(-64)/Linux systems, such as CLEAR.
 * The mapping for other versions of Unix, such as FreeBSD, Mac OS X, or
 * Solaris, differ!
 */
static const char *const signame[NSIG] = {
	"Signal 0",
	"HUP",				/* SIGHUP */
	"INT",				/* SIGINT */
	"QUIT",				/* SIGQUIT */
	"ILL",				/* SIGILL */
	"TRAP",				/* SIGTRAP */
	"ABRT",				/* SIGABRT */
	"BUS",				/* SIGBUS */
	"FPE",				/* SIGFPE */
	"KILL",				/* SIGKILL */
	"USR1",				/* SIGUSR1 */
	"SEGV",				/* SIGSEGV */
	"USR2",				/* SIGUSR2 */
	"PIPE",				/* SIGPIPE */
	"ALRM",				/* SIGALRM */
	"TERM",				/* SIGTERM */
	"STKFLT",			/* SIGSTKFLT */
	"CHLD",				/* SIGCHLD */
	"CONT",				/* SIGCONT */
	"STOP",				/* SIGSTOP */
	"TSTP",				/* SIGTSTP */
	"TTIN",				/* SIGTTIN */
	"TTOU",				/* SIGTTOU */
	"URG",				/* SIGURG */
	"XCPU",				/* SIGXCPU */
	"XFSZ",				/* SIGXFSZ */
	"VTALRM",			/* SIGVTALRM */
	"PROF",				/* SIGPROF */
	"WINCH",			/* SIGWINCH */
	"IO",				/* SIGIO */
	"PWR",				/* SIGPWR */
	"Signal 31"
};

// You must implement the following functions:

static int	builtin_cmd(char **argv);
static void	do_bgfg(char **argv);
static void	eval(const char *cmdline);
static void	initpath(const char *pathstr);
static void	waitfg(pid_t pid);

static void	sigchld_handler(int signum);
static void	sigint_handler(int signum);
static void	sigtstp_handler(int signum);

// We are providing the following functions to you:

static int	parseline(const char *cmdline, char **argv); 

static void	sigquit_handler(int signum);

static int	addjob(JobP jobs, pid_t pid, int state, const char *cmdline);
static void	clearjob(JobP job);
static int	deletejob(JobP jobs, pid_t pid); 
static pid_t	fgpid(JobP jobs);
static JobP	getjobjid(JobP jobs, int jid); 
static JobP	getjobpid(JobP jobs, pid_t pid);
static void	initjobs(JobP jobs);
static void	listjobs(JobP jobs);
static int	maxjid(JobP jobs); 
static int	pid2jid(pid_t pid); 

static void	app_error(const char *msg);
static void	unix_error(const char *msg);
static void	usage(void);

static void	Sio_error(const char s[]);
static ssize_t	Sio_putl(long v);
static ssize_t	Sio_puts(const char s[]);
static void	sio_error(const char s[]);
static void	sio_ltoa(long v, char s[], int b);
static ssize_t	sio_putl(long v);
static ssize_t	sio_puts(const char s[]);
static void	sio_reverse(char s[]);
static size_t	sio_strlen(const char s[]);

/*
 * Requires:
 *   argc, the number of characters in argv, an array of strings representing
 *   a tokenized command line.
 *
 * Effects:
 *   Initializes signal handlers, then continuously checks the command line
 *   for new input. Acts as a shell for input, printing the "tsh> " prompt and 
 *   then calling eval and parseline to evaluate the input until told to 
 *   terminate using the builtin command "quit". 
 */
int
main(int argc, char **argv) 
{
	struct sigaction action;
	int c;
	char cmdline[MAXLINE];
	char *path = NULL;
	bool emit_prompt = true;	// Emit a prompt by default.

	/*
	 * Redirect stderr to stdout (so that driver will get all output
	 * on the pipe connected to stdout).
	 */
	dup2(1, 2);

	// Parse the command line.
	while ((c = getopt(argc, argv, "hvp")) != -1) {
		switch (c) {
		case 'h':             // Print a help message.
			usage();
			break;
		case 'v':             // Emit additional diagnostic info.
			verbose = true;
			break;
		case 'p':             // Don't print a prompt.
			// This is handy for automatic testing.
			emit_prompt = false;
			break;
		default:
			usage();
		}
	}

	/*
	 * Install sigint_handler() as the handler for SIGINT (ctrl-c).  SET
	 * action.sa_mask TO REFLECT THE SYNCHRONIZATION REQUIRED BY YOUR
	 * IMPLEMENTATION OF sigint_handler().
	 */
	action.sa_handler = sigint_handler;
	action.sa_flags = SA_RESTART;
	if (sigemptyset(&action.sa_mask) == -1) {
		unix_error("sigemptyset error");
	}
	if (sigaddset(&action.sa_mask, SIGCHLD) == -1) {
		unix_error("sigaddset error in main");
	}
	if (sigaction(SIGINT, &action, NULL) < 0)
		unix_error("sigaction error");
	

	/*
	 * Install sigtstp_handler() as the handler for SIGTSTP (ctrl-z).  SET
	 * action.sa_mask TO REFLECT THE SYNCHRONIZATION REQUIRED BY YOUR
	 * IMPLEMENTATION OF sigtstp_handler().
	 */
	action.sa_handler = sigtstp_handler;
	action.sa_flags = SA_RESTART;
	if (sigemptyset(&action.sa_mask) == -1) {
		unix_error("sigemptyset error");
	}
	if (sigaddset(&action.sa_mask, SIGCHLD) == -1) {
		unix_error("sigaddset error in main");
	}
	if (sigaction(SIGTSTP, &action, NULL) < 0)
		unix_error("sigaction error");
	
	/*
	 * Install sigchld_handler() as the handler for SIGCHLD (terminated or
	 * stopped child).  SET action.sa_mask TO REFLECT THE SYNCHRONIZATION
	 * REQUIRED BY YOUR IMPLEMENTATION OF sigchld_handler().
	 */
	action.sa_handler = sigchld_handler;
	action.sa_flags = SA_RESTART;
	if (sigemptyset(&action.sa_mask) == -1) {
		unix_error("sigemptyset error");
	}
	if (sigaddset(&action.sa_mask, SIGINT) == -1) {
		unix_error("sigaddset error"); 
	}
	if (sigaddset(&action.sa_mask, SIGTSTP) == -1) {
		unix_error("sigaddset error");
	}
	if (sigaction(SIGCHLD, &action, NULL) < 0)
		unix_error("sigaction error");
	
	/*
	 * Install sigquit_handler() as the handler for SIGQUIT.  This handler
	 * provides a clean way for the test harness to terminate the shell.
	 * Preemption of the processor by the other signal handlers during
	 * sigquit_handler() does no harm, so action.sa_mask is set to empty.
	 */
	action.sa_handler = sigquit_handler;
	action.sa_flags = SA_RESTART;
	sigemptyset(&action.sa_mask);
	if (sigaction(SIGQUIT, &action, NULL) < 0)
		unix_error("sigaction error");
	
	// Initialize the search path.
	path = getenv("PATH");
	initpath(path);
	
	// Initialize the jobs list.
	initjobs(jobs);

	// Execute the shell's read/eval loop.
	while (true) {
		
		// Read the command line.
		if (emit_prompt) {
			printf("%s", prompt);
			fflush(stdout);
		}
		if ((fgets(cmdline, MAXLINE, stdin) == NULL) && ferror(stdin))
			app_error("fgets error");
		if (feof(stdin)) { // End of file (ctrl-d)
			fflush(stdout);
			exit(0);
		}

		// Evaluate the command line.
		eval(cmdline);
		fflush(stdout);
		fflush(stdout);
	}

	// Control never reaches here.
	assert(false);
}
  
/* 
 * eval - Evaluate the command line that the user has just typed in.
 * 
 * If the user has requested a built-in command (quit, jobs, bg or fg)
 * then execute it immediately.  Otherwise, fork a child process and
 * run the job in the context of the child.  If the job is running in
 * the foreground, wait for it to terminate and then return.  Note:
 * each child process must have a unique process group ID so that our
 * background children don't receive SIGINT (SIGTSTP) from the kernel
 * when we type ctrl-c (ctrl-z) at the keyboard.  
 *
 * Requires:
 *   cmdline: The text from the command line to be passed to parseline
 *
 * Effects:
 *   First checks if the cmdline contains a built in command. If so, 
 *	 execute it and move on to the next command line. If not, we assume 
 *   that the first argument must be a command, and we run the command on 
 *   the paths in initpath. Fork to a child process, and parent process
 *   will wait depending on whether or not parseline returns a background
 *   job or foreground job. Calls waitfg to do this. 
 */
static void
eval(const char *cmdline) 
{
	char *argv[MAXARGS];
	int bg = parseline(cmdline, argv);
	pid_t pid; //, childpid;

	if (argv[0] == NULL) {
		// Ignore empty console input.
		return;
	}


	if (strcmp(argv[0],"quit") == 0 || (strcmp(argv[0],"jobs") == 0 ||
		strcmp(argv[0],"bg") == 0 || strcmp(argv[0],"fg") == 0)) {
		builtin_cmd(argv);
		return;
	} 

	// Not a built-in command,

	sigset_t temp; 
	if (sigaddset(&temp, SIGCHLD) == -1) {
		unix_error("error on sigaddset in eval"); 
	}

	
	if (sigprocmask(SIG_BLOCK, &temp, NULL) == -1) {
		unix_error("error on sigprocmask in eval");
	}
	// Blocking here to avoid datarace if child executes before addjob.
	pid = fork();

	if (pid == 0) {
		// Child
		setpgid(0,0);
		if (sigprocmask(SIG_UNBLOCK, &temp, NULL) == -1) {
			unix_error("error on sigprocmask in eval");
		}

		// Try to execute on every path in path. 

		struct list *head;
		execve(argv[0],argv,environ);
		char* temppath;
		for (head = paths; head != NULL && head->name != NULL; head = head->tail_list) {
			temppath = malloc(strlen(head->name) * 4 + strlen(argv[0]) * 4 + 8);
			temppath = strcpy(temppath, head->name);
			temppath = strcat(temppath,"/");
			temppath = strcat(temppath, argv[0]);
			execve(temppath, argv, environ);
			//Sio_puts(temppath);
			//Sio_puts("\n");
			free(temppath);

		}
		// Should never make it past the execve calls unless command DNE.
		Sio_puts(argv[0]);
		Sio_puts(": Command not found\n");
		exit(0);
		
	} else {
		// Parent
		if (addjob(jobs, pid, bg+1, cmdline) == 0) {
			// addjob can fail if we have more than the allotted number of jobs
			// in the jobs struct. 
			return;
		} 

		// Continue handling the job. 
		if (sigprocmask(SIG_UNBLOCK, &temp, NULL) == -1) {
			unix_error("error on sigprocmask in eval");
		}
		if (bg == 0) {
			//Run in foreground
			waitfg(pid);
		} else {
			// Here we print the job information after adding.
			printf("[%i] (%i) %s", getjobpid(jobs,pid)->jid, pid, cmdline);
		}
	}
	return; // Either is a bg task, or fg task finished. 
}


/* 
 * parseline - Parse the command line and build the argv array.
 *
 * Requires:
 *   "cmdline" is a NUL ('\0') terminated string with a trailing
 *   '\n' character.  "cmdline" must contain less than MAXARGS
 *   arguments.
 *
 * Effects:
 *   Builds "argv" array from space delimited arguments on the command line.
 *   The final element of "argv" is set to NULL.  Characters enclosed in
 *   single quotes are treated as a single argument.  Returns true if
 *   the user has requested a BG job and false if the user has requested
 *   a FG job.
 */
static int
parseline(const char *cmdline, char **argv) 
{
	int argc;                   // number of args
	int bg;                     // background job?
	static char array[MAXLINE]; // local copy of command line
	char *buf = array;          // ptr that traverses command line
	char *delim;                // points to first space delimiter

	strcpy(buf, cmdline);

	// Replace trailing '\n' with space.
	buf[strlen(buf) - 1] = ' ';

	// Ignore leading spaces.
	while (*buf != '\0' && *buf == ' ')
		buf++;

	// Build the argv list.
	argc = 0;
	if (*buf == '\'') {
		buf++;
		delim = strchr(buf, '\'');
	} else
		delim = strchr(buf, ' ');
	while (delim != NULL) {
		argv[argc++] = buf;
		*delim = '\0';
		buf = delim + 1;
		while (*buf != '\0' && *buf == ' ')	// Ignore spaces.
			buf++;
		if (*buf == '\'') {
			buf++;
			delim = strchr(buf, '\'');
		} else
			delim = strchr(buf, ' ');
	}
	argv[argc] = NULL;

	// Ignore blank line.
	if (argc == 0)
		return (1);

	// Should the job run in the background?
	if ((bg = (*argv[argc - 1] == '&')) != 0)
		argv[--argc] = NULL;

	return (bg);
}

/* 
 * builtin_cmd - If the user has typed a built-in command then execute
 *  it immediately.  
 *
 * Requires:
 *   argv, an array of strings representing a tokenized commandline
 *
 * Effects:
 *   Implements the builtin commands: bg and fg call do_bgfg, quit exits, and
 *   jobs calls listjobs.
 */
static int
builtin_cmd(char **argv) 
{
	if(strcmp(argv[0], "bg") == 0 || strcmp(argv[0], "fg") == 0) {
		do_bgfg(argv);
	} else if(strcmp(argv[0], "quit") == 0) {
		exit(0);
	} else if(strcmp(argv[0], "jobs") == 0) {
		listjobs(jobs);
	} else {
		app_error("Not a built-in command");
		return(1);
	}
	return(0);
}

/* 
 * do_bgfg - Execute the built-in bg and fg commands.
 *
 * Requires:
 *   argv, an array of string representing the commandline in tokens 
 *
 * Effects:
 *   Implements the bg and fg builtin commands. Will take a jobid or a PID,
 *   then use the kill command to send SIGCONT to those jobs. Lots of error 
 *   handling to make sure that the ids are of the correct format and 
 *   actually have associated job pointers. 
 */
static void
do_bgfg(char **argv) 
{
	char* job = argv[1];
	bool isPid = true; 
	int id;
	pid_t pid;
	if (job[0] == '%') {
		isPid = false;
		memmove(job, job+1, strlen(job));
	}
	id = atoi(job);
	pid = (pid_t) id;
	if (id < 0) {
		printf("%s: argument must be a PID or %%jobid\n", argv[0]);
		return;
	}

	if (strcmp(argv[0], "bg") == 0) {
		// Send SIGCONT to the specified job.
		if (isPid) {
			if (getjobpid(jobs, pid) == NULL) {
				printf("(%i) No such process\n", id);
				return;
			}
			printf("[%i] (%i) %s", getjobpid(jobs,pid)->jid, pid, getjobpid(jobs,pid)->cmdline);
			getjobpid(jobs,pid)->state = BG;
			if (kill(pid, SIGCONT) == 1) {
				unix_error("Error sending SIGCONT in do_bgfg");
			} 
		} else {
			if (getjobjid(jobs,id) == NULL) {
				printf("%%%i No such job\n", id);
				return;
			}
			pid = getjobjid(jobs, id)->pid;
			printf("[%i] (%i) %s", id, pid, getjobpid(jobs,pid)->cmdline);
			getjobpid(jobs,pid)->state = BG;
			if (kill(pid, SIGCONT) == 1) {
				unix_error("Error sending SIGCONT in do_bgfg");
			}
		}
	} else if (strcmp(argv[0], "fg") == 0) {
		// Send SIGCONT to the specified job.
		if (isPid) {
			if (getjobpid(jobs, pid) == NULL) {
				printf("(%i) No such process\n", id);
				return;
			}
			getjobpid(jobs,pid)->state = FG;
			if (kill(pid, SIGCONT) == 1) {
				unix_error("Error sending SIGCONT in do_bgfg");
			}
		} else {
			if (getjobjid(jobs,id) == NULL) {
				printf("%%%i No such job\n", id);
			}
			pid = getjobjid(jobs, id)->pid;
			getjobpid(jobs,pid)->state = FG;
			if (kill(pid, SIGCONT) == 1) {
				unix_error("Error sending SIGCONT in do_bgfg");
				return;
			}
		}
		// Wait for current foreground process to finish.
		waitfg(pid);
	} else {
		app_error("Not a bg or fg command");
	}
}

/* 
 * waitfg - Block until process pid is no longer the foreground process.
 *
 * Requires:
 *   A pid, which represents the process id of the process we want to wait on.
 *
 * Effects:
 *   Uses the child handler to ensure that the job is deleted from the jobs 
 *   array when the child finishes normally or is terminated/stopped. Uses
 *   a while loop to sleep forever until the childhandler reaps. 
 */
static void
waitfg(pid_t pid)
{
	int fpid;
	fpid = fgpid(jobs);
	while (fpid != 0 && pid == fgpid(jobs)) {
		fpid = (fgpid(jobs));
		sleep(1);
	}

}

/* 
 * initpath - Perform all necessary initialization of the search path,
 *  which may be simply saving the path.
 *
 * Requires:
 *   "pathstr" is a valid search path.
 *
 * Effects:
 *   Creates and stores a linkedlist in the global field paths. Represents a 
 *   list of all the possible paths to try and execute a command in.
 */
static void
initpath(const char *pathstr)
{	
	struct list *pathList = malloc(sizeof(struct list));
	char *original = malloc((strlen(pathstr) + 1) * 4);
	strcpy(original, pathstr);
	char *found;

	while ((found = strsep(&original,":")) != NULL) {
		if (strcmp(found, "") == 0) {
			getcwd(found, sizeof(found));
		}
		struct list *pathListTemp = malloc(sizeof(struct list));
		pathListTemp->name = found;
		pathListTemp->tail_list = pathList;
		pathList = pathListTemp;
	}

	paths = pathList;

	if (verbose) {
		struct list *head;
		for (head = paths; head != NULL; head = head->tail_list) {
			printf(head->name);
			printf("\n");
		}
	}
}

/*
 * The signal handlers follow.
 */

/* 
 * sigchld_handler - The kernel sends a SIGCHLD to the shell whenever
 *  a child job terminates (becomes a zombie), or stops because it
 *  received a SIGSTOP or SIGTSTP signal.  The handler reaps all
 *  available zombie children, but doesn't wait for any other
 *  currently running children to terminate.  
 *
 * Requires:
 *   Signum, although this input isn't used nor necessary
 *
 * Effects:
 *   Uses waitpid to check if a job was terminated or stopped, then reaps
 *   the child and prints the required message. Deletes the job from the 
 *   jobs array when done, so that waitfg can stop sleeping. 
 */
static void
sigchld_handler(int signum)
{
	pid_t pid;
	int status;

	// Don't know what to do with signum
	(void)signum;


	while ((pid = waitpid(-1, &status, WNOHANG | WUNTRACED)) > 0) {
		// Reap Children mwahaha
		if (WIFSTOPPED(status)) {
			Sio_puts("Job [");
			Sio_putl(getjobpid(jobs,pid)->jid);
			Sio_puts("] (");
			Sio_putl(pid);
			Sio_puts(") stopped by signal SIG");
			Sio_puts(signame[WSTOPSIG(status)]);
			Sio_puts("\n");
			getjobpid(jobs,pid)->state = 3; //3 = ST
		} else if ((status)) {
			Sio_puts("Job [");
			Sio_putl(getjobpid(jobs,pid)->jid);
			Sio_puts("] (");
			Sio_putl(pid);
			Sio_puts(") terminated by signal SIG");
			Sio_puts(signame[WTERMSIG(status)]);
			Sio_puts("\n");
			deletejob(jobs, pid);
		} else {
			deletejob(jobs,pid);
		}
	}

}

/* 
 * sigint_handler - The kernel sends a SIGINT to the shell whenever the
 *  user types ctrl-c at the keyboard.  Catch it and send it along
 *  to the foreground job.  
 *
 * Requires:
 *   signum, the signal (should be sigint) to pass along.
 *
 * Effects:
 *   Forwards sigint to all foreground processes. 
 */
static void
sigint_handler(int signum)
{

	if (fgpid(jobs) != 0) {
		if (getpgid(fgpid(jobs)) != -1) {
			if (kill(getpgid(fgpid(jobs)) * -1, signum) == 1) {
				Sio_error("Error sending sigint in handler");
			}
		}
	}
	
}

/*
 * sigtstp_handler - The kernel sends a SIGTSTP to the shell whenever
 *  the user types ctrl-z at the keyboard.  Catch it and suspend the
 *  foreground job by sending it a SIGTSTP.  
 *
 * Requires:
 *   signum, the signal (should be sigtstp) to pass along.
 *
 * Effects:
 *   Forwards sigtstp to all forground processes.
 */
static void
sigtstp_handler(int signum)
{

	// Prevent an "unused parameter" warning.
	if (fgpid(jobs) != 0) {
		if (getpgid(fgpid(jobs)) != -1) {
			if (kill(getpgid(fgpid(jobs)) * -1, signum) == 1) {
				Sio_error("Error sending sigtstp in handler");
			}
		}
	}
	
	
}

/*
 * sigquit_handler - The driver program can gracefully terminate the
 *  child shell by sending it a SIGQUIT signal.
 *
 * Requires:
 *   "signum" is SIGQUIT.
 *
 * Effects:
 *   Terminates the program.
 */
static void
sigquit_handler(int signum)
{

	// Prevent an "unused parameter" warning.
	(void)signum;
	Sio_puts("Terminating after receipt of SIGQUIT signal\n");
	_exit(1);
}

/*
 * This comment marks the end of the signal handlers.
 */

/*
 * The following helper routines manipulate the jobs list.
 */

/*
 * Requires:
 *   "job" points to a job structure.
 *
 * Effects:
 *   Clears the fields in the referenced job structure.
 */
static void
clearjob(JobP job)
{

	job->pid = 0;
	job->jid = 0;
	job->state = UNDEF;
	job->cmdline[0] = '\0';
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Initializes the jobs list to an empty state.
 */
static void
initjobs(JobP jobs)
{
	int i;

	for (i = 0; i < MAXJOBS; i++)
		clearjob(&jobs[i]);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Returns the largest allocated job ID.
 */
static int
maxjid(JobP jobs) 
{
	int i, max = 0;

	for (i = 0; i < MAXJOBS; i++)
		if (jobs[i].jid > max)
			max = jobs[i].jid;
	return (max);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures, and "cmdline" is
 *   a properly terminated string.
 *
 * Effects: 
 *   Adds a job to the jobs list. 
 */
static int
addjob(JobP jobs, pid_t pid, int state, const char *cmdline)
{
	int i;
    
	if (pid < 1)
		return (0);
	for (i = 0; i < MAXJOBS; i++) {
		if (jobs[i].pid == 0) {
			jobs[i].pid = pid;
			jobs[i].state = state;
			jobs[i].jid = nextjid++;
			if (nextjid > MAXJOBS)
				nextjid = 1;
			// Remove the "volatile" qualifier using a cast.
			strcpy((char *)jobs[i].cmdline, cmdline);
			if (verbose) {
				printf("Added job [%d] %d %s\n", jobs[i].jid,
				    (int)jobs[i].pid, jobs[i].cmdline);
			}
			return (1);
		}
	}
	printf("Tried to create too many jobs\n");
	return (0);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Deletes a job from the jobs list whose PID equals "pid".
 */
static int
deletejob(JobP jobs, pid_t pid) 
{
	int i;

	if (pid < 1)
		return (0);
	for (i = 0; i < MAXJOBS; i++) {
		if (jobs[i].pid == pid) {
			clearjob(&jobs[i]);
			nextjid = maxjid(jobs) + 1;
			return (1);
		}
	}
	return (0);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Returns the PID of the current foreground job or 0 if no foreground
 *   job exists.
 */
static pid_t
fgpid(JobP jobs)
{
	int i;

	for (i = 0; i < MAXJOBS; i++)
		if (jobs[i].state == FG)
			return (jobs[i].pid);
	return (0);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Returns a pointer to the job structure with process ID "pid" or NULL if
 *   no such job exists.
 */
static JobP
getjobpid(JobP jobs, pid_t pid)
{
	int i;

	if (pid < 1)
		return (NULL);
	for (i = 0; i < MAXJOBS; i++)
		if (jobs[i].pid == pid)
			return (&jobs[i]);
	return (NULL);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Returns a pointer to the job structure with job ID "jid" or NULL if no
 *   such job exists.
 */
static JobP
getjobjid(JobP jobs, int jid) 
{
	int i;

	if (jid < 1)
		return (NULL);
	for (i = 0; i < MAXJOBS; i++)
		if (jobs[i].jid == jid)
			return (&jobs[i]);
	return (NULL);
}

/*
 * Requires:
 *   Nothing.
 *
 * Effects:
 *   Returns the job ID for the job with process ID "pid" or 0 if no such
 *   job exists.
 */
static int
pid2jid(pid_t pid) 
{
	int i;

	if (pid < 1)
		return (0);
	for (i = 0; i < MAXJOBS; i++)
		if (jobs[i].pid == pid)
			return (jobs[i].jid);
	return (0);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Prints the jobs list.
 */
static void
listjobs(JobP jobs) 
{
	int i;

	for (i = 0; i < MAXJOBS; i++) {
		if (jobs[i].pid != 0) {
			printf("[%d] (%d) ", jobs[i].jid, (int)jobs[i].pid);
			switch (jobs[i].state) {
			case BG: 
				printf("Running ");
				break;
			case FG: 
				printf("Foreground ");
				break;
			case ST: 
				printf("Stopped ");
				break;
			default:
				printf("listjobs: Internal error: "
				    "job[%d].state=%d ", i, jobs[i].state);
			}
			printf("%s", jobs[i].cmdline);
		}
	}
}

/*
 * This comment marks the end of the jobs list helper routines.
 */

/*
 * Other helper routines follow.
 */

/*
 * Requires:
 *   Nothing.
 *
 * Effects:
 *   Prints a help message.
 */
static void
usage(void) 
{

	printf("Usage: shell [-hvp]\n");
	printf("   -h   print this message\n");
	printf("   -v   print additional diagnostic information\n");
	printf("   -p   do not emit a command prompt\n");
	exit(1);
}

/*
 * Requires:
 *   "msg" is a properly terminated string.
 *
 * Effects:
 *   Prints a Unix-style error message and terminates the program.
 */
static void
unix_error(const char *msg)
{

	fprintf(stdout, "%s: %s\n", msg, strerror(errno));
	exit(1);
}

/*
 * Requires:
 *   "msg" is a properly terminated string.
 *
 * Effects:
 *   Prints "msg" and terminates the program.
 */
static void
app_error(const char *msg)
{

	fprintf(stdout, "%s\n", msg);
	exit(1);
}

/*
 * Requires:
 *   The character array "s" is sufficiently large to store the ASCII
 *   representation of the long "v" in base "b".
 *
 * Effects:
 *   Converts a long "v" to a base "b" string, storing that string in the
 *   character array "s" (from K&R).  This function can be safely called by
 *   a signal handler.
 */
static void
sio_ltoa(long v, char s[], int b)
{
	int c, i = 0;

	do
		s[i++] = (c = v % b) < 10 ? c + '0' : c - 10 + 'a';
	while ((v /= b) > 0);
	s[i] = '\0';
	sio_reverse(s);
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Reverses a string (from K&R).  This function can be safely called by a
 *   signal handler.
 */
static void
sio_reverse(char s[])
{
	int c, i, j;

	for (i = 0, j = sio_strlen(s) - 1; i < j; i++, j--) {
		c = s[i];
		s[i] = s[j];
		s[j] = c;
	}
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Computes and returns the length of the string "s".  This function can be
 *   safely called by a signal handler.
 */
static size_t
sio_strlen(const char s[])
{
	size_t i = 0;

	while (s[i] != '\0')
		i++;
	return (i);
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Prints the long "v" to stdout using only functions that can be safely
 *   called by a signal handler, and returns either the number of characters
 *   printed or -1 if the long could not be printed.
 */
static ssize_t
sio_putl(long v)
{
	char s[128];
    
	sio_ltoa(v, s, 10);
	return (sio_puts(s));
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Prints the string "s" to stdout using only functions that can be safely
 *   called by a signal handler, and returns either the number of characters
 *   printed or -1 if the string could not be printed.
 */
static ssize_t
sio_puts(const char s[])
{

	return (write(STDOUT_FILENO, s, sio_strlen(s)));
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Prints the string "s" to stdout using only functions that can be safely
 *   called by a signal handler, and exits the program.
 */
static void
sio_error(const char s[])
{

	sio_puts(s);
	_exit(1);
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Prints the long "v" to stdout using only functions that can be safely
 *   called by a signal handler.  Either returns the number of characters
 *   printed or exits if the long could not be printed.
 */
static ssize_t
Sio_putl(long v)
{
	ssize_t n;
  
	if ((n = sio_putl(v)) < 0)
		sio_error("Sio_putl error");
	return (n);
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Prints the string "s" to stdout using only functions that can be safely
 *   called by a signal handler.  Either returns the number of characters
 *   printed or exits if the string could not be printed.
 */
static ssize_t
Sio_puts(const char s[])
{
	ssize_t n;
  
	if ((n = sio_puts(s)) < 0)
		sio_error("Sio_puts error");
	return (n);
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Prints the string "s" to stdout using only functions that can be safely
 *   called by a signal handler, and exits the program.
 */
static void
Sio_error(const char s[])
{

	sio_error(s);
}

// Prevent "unused function" and "unused variable" warnings.
static const void *dummy_ref[] = { Sio_error, Sio_putl, addjob, builtin_cmd,
    deletejob, do_bgfg, dummy_ref, fgpid, getjobjid, getjobpid, listjobs,
    parseline, pid2jid, signame, waitfg };
