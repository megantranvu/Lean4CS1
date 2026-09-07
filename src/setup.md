# Greetingss

There is good reason today to believe that every serious
software engineer of the future will be expected to know
how to use and produce software artifacts that, in a single
language, intelligibly express everything from the abstract
mathematics of the application domain, to low-level hardware
operational dynamics, inflected with machine-verified proofs
blended seamlessly throughout, attesting to the consistency
of every single detail of the entire construct.

The magnitude of this impending paradigm shift in programming
is of a different nature than in the past. Binary, assembly, 
imperative programming, functional programming, structured 
programming, object-oriented programming, parallel programming, 
concurrent programming, SIMD programming. The are all languages
in which one can express only half of the world at hand in any
serious setting. They are computation languages. What they lack
are facilities for mathematical abtsract or deductive reasoning,
which are basically all of it for software specification and 
verification.  



now before us is far greater
those those 

computatational software
development  in traditional programming,  







 system requirements,
necessarily expressed in the terms of application domain;
specifications concerning particular machinery to be built;
and ordinary computation, with continual checking of  
to  
implementations in the low-level formalisms
of, say, imperative programming, but also to express the
abstract mathematics of the application domain itself,
the definitions of terms for which are prerequite to the
expression of some particular system intended to operate
in, with, and on that domain. 

with the 
the
domain 
the been trained to
handle the formal mathematics of the domain of discourse  

be will be trained to deal with the abstract
mathematics 

A premise of this course is that future programmers will
have to understand how to weave abstract mathematical
formal specifications and
corresponding implementations within single   


The goal of this course on *programming* is to equip each
student with cognitive skills and performance capabilities
to acquire a strong cognitive grasp of the 
affordances provided by dependent type theory and how to use
them to compose astoundingly rich formal abstractions

computation, reasoning, 


 mental model of what that term means grounded not (only) in notions of *computation*


an understanding of this term that encompasses not
just types of data and operations partticular to data according
to its type 




This online book is generated from literate code (see Knuth) written
in the dependently typed, mathematics-supporting programming language
called Lean 4. The code is distributed from a GitHub repository.

At the top of the page, from the left, one finds a sequence of icons.
The hamburger (three-line-stack) menu shows/hides the table of contents;
the paintbrush icon is for changing the presentation color scheme; the
magnifying icon is for text search over this book; the printer icon is
for printing it (or saving it as a PDF for offline reading); and the last,
GitHub, icon takes you to the GitHub repo where this book is stored.

Everything in this course runs inside a Docker **development container,**
a preconfigured Linux environment defined by files in this repository, that
Docker builds on your laptop. You do not install Lean, Mathlib, or the book
tooling yourself. You install Docker and VS Code, open this project, and let
the container supply the rest.

The best way to use this book is to open it in a browser within
VSCode, right alongside the Lean 4 code that was processed to create
it. To be able to do that, follow the directions here. In a nutshell,
you will fork our repo, clone your fork of our repo, open your clone
in VSCode; activate the Dev Containers VSCode plug-in; start up the
"container"; then arrange your editor layout. Voila! Up and running.

The benefit is that every student has an identical environment with fairly low effort.

Work through the steps in order. Step 4 takes the longest; start it before
you need it.

## 1. Install the prerequisites

You need four things on your laptop. Install them in this order.

|     | What                                                              | Notes                                                                                        |
| --- | ----------------------------------------------------------------- | -------------------------------------------------------------------------------------------- |
| 1   | A [GitHub account](https://github.com/signup)                     | Free. Use an address you check.                                                              |
| 2   | [Git](https://git-scm.com/downloads)                              | Already present on macOS and most Linux systems. Check with `git --version`.                 |
| 3   | [Docker Desktop](https://www.docker.com/products/docker-desktop/) | The container engine. Choose the build matching your chip — Apple Silicon or Intel on macOS. |
| 4   | [Visual Studio Code](https://code.visualstudio.com/)              | The editor.                                                                                  |

Then install one VS Code extension by hand — the
[**Dev Containers**](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers)
extension (`ms-vscode-remote.remote-containers`). Open the Extensions view
(`Cmd+Shift+X` / `Ctrl+Shift+X`), search for "Dev Containers", and install it.
Every *other* extension you need, including Lean 4, is installed automatically
inside the container.

**Give Docker enough room.** This container requests 10 GB of memory, and a
built Mathlib occupies roughly 7 GB on disk. Before continuing:

- Open Docker Desktop → **Settings** → **Resources**.
- Set memory to **at least 10 GB** (12 GB or more if your laptop has 16 GB).
- Confirm you have **15 GB of free disk space**.

On Windows, Docker Desktop must use the **WSL 2** backend; its installer will
offer to set this up.

Start Docker Desktop and leave it running. The container cannot start if the
Docker engine is not running — the single most common setup failure.

## 2. Fork this repository

A *fork* is your own copy of the repository on GitHub. You will do your work
in your fork, so your changes are yours and cannot disturb the course
repository.

1. Go to **[github.com/kevinsullivan/Lean4CS1](https://github.com/kevinsullivan/Lean4CS1)**.
2. Click **Fork** (top right).
3. Leave the name as `Lean4CS1` and click **Create fork**.

You now have `https://github.com/YOUR-USERNAME/Lean4CS1`.

## 3. Clone your fork and open it in VS Code

### Windows users: configure Git first

Do this **before you clone**. These settings affect how files are written to
disk during the clone, so applying them afterward means re-cloning.

This repository is Linux-based: every file in it ends its lines with a single
newline (LF), and the container runs Linux. Git for Windows, by default,
converts line endings to Windows style (CRLF) on checkout. That conversion
breaks things inside the container — shell scripts fail with errors like
`bash\r: command not found`, and `scripts/convert.py` and the `Makefile`
misbehave in ways whose cause is not obvious from the symptom.

Open **Git Bash** or **PowerShell** and run:

```bash
git config --global core.autocrlf false
git config --global core.eol lf
git config --global core.longpaths true
```

What each one does:

| Setting               | Why                                                                                                                                                                             |
| --------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `core.autocrlf false` | Stops Git rewriting LF to CRLF on checkout. Files stay exactly as the repository stores them.                                                                                   |
| `core.eol lf`         | Makes LF the line ending Git writes, so files you create match the rest of the repository.                                                                                      |
| `core.longpaths true` | Lifts Windows' 260-character path limit. Mathlib's nested paths under `.lake/packages/` exceed it, and without this the toolchain fails with confusing "file not found" errors. |

Confirm they took effect:

```bash
git config --global --list | findstr core
```

You should see `core.autocrlf=false`, `core.eol=lf`, and
`core.longpaths=true`.

**Set your editor to write LF too.** VS Code shows the current line ending in
the status bar, at the right, as `LF` or `CRLF`. To make LF the default, open
Settings (`Ctrl+,`), search for **Files: Eol**, and choose `\n`.

**Already cloned with the wrong settings?** Apply the three settings above,
then delete the folder and clone again. Re-checking-out in place will not
reliably fix line endings that are already on disk.

**A note on where you clone.** Everything below works from an ordinary Windows
folder such as `C:\Users\you\Lean4CS1`. If builds feel slow, the cause is
usually that Docker reaches Windows files through a translation layer. Cloning
into the WSL 2 filesystem instead — from a WSL terminal, into your Linux home
directory — is substantially faster. Do that only if you are comfortable with
WSL; it is a performance improvement, not a requirement.

### Clone

Clone *your fork*, not the original. Substitute your GitHub username:

```bash
git clone https://github.com/YOUR-USERNAME/Lean4CS1.git
cd Lean4CS1
code .
```

If `code` is not a recognized command, open VS Code, press
`Cmd+Shift+P` / `Ctrl+Shift+P`, run **Shell Command: Install 'code' command in
PATH**, then try again — or simply use **File → Open Folder** and select the
cloned directory.

While you are here, connect your fork back to the course repository so you can
pull in updates later:

```bash
git remote add upstream https://github.com/kevinsullivan/Lean4CS1.git
```

## 4. Reopen the project in the container

With the project open in VS Code, a notification should appear in the
lower-right corner:

> **Folder contains a Dev Container configuration file. Reopen folder to
> develop in a container.**

Click **Reopen in Container**.

If the notification does not appear, press `Cmd+Shift+P` / `Ctrl+Shift+P` and
run **Dev Containers: Reopen in Container**.

**The first build takes a long time — plan on 15 to 45 minutes**, depending on
your laptop and network. Docker is downloading a base image and building the
environment. Click **show log** in the notification if you want to watch. Do
not close VS Code; interrupting it means starting over.

Later launches reuse the built image and take well under a minute.

You know it worked when the green indicator in the bottom-left corner of the
VS Code window reads **Dev Container: CS1**. Open a terminal
(`` Ctrl+` ``, or Terminal → New Terminal) — you are now a user named `dev`
inside Linux, whatever your laptop actually runs.

## 5. Install the Lean toolchain and Mathlib

Two steps remain, both run in the VS Code terminal *inside* the container.

**Open any Lean file first** — for example
`FPCourse/T01_ExpressionsFunctionsRecursion/Week00_AlgebraicTypes.lean`. The Lean 4 extension activates,
notices the `lean-toolchain` file, and installs the exact compiler version
this course uses. A progress notice appears in the status bar. Wait for it to
finish, then confirm:

```bash
lean --version
```

It should report the version named in `lean-toolchain`.

**Then fetch prebuilt Mathlib.** Mathlib is large; compiling it from source
takes hours, and there is no reason to. Download the prebuilt libraries
instead:

```bash
lake exe cache get
```

This retrieves several gigabytes — expect ten minutes or so on a good
connection. Once it finishes, compile the course sources:

```bash
lake build
```

The first run works through the course files; later runs only rebuild what
changed. If `lake build` completes without errors, your environment is
correct and complete.

> **If `lake exe cache get` fails or you skip it**, `lake build` will try to
> compile Mathlib from scratch. If a build seems to run forever with
> unfamiliar file names streaming past, stop it with `Ctrl+C`, run
> `lake exe cache get`, and try again.

## 6. Read the book beside the code

The intended way to study is the rendered book on one side of the screen and
the live, type-checked Lean source on the other.

### Three commands keep the book current

You never call mdBook directly. Three `make` targets, run from the project
root in the container terminal, cover everything you need:

| Command      | What it does                                                                                                                                     |
| ------------ | ------------------------------------------------------------------------------------------------------------------------------------------------ |
| `make build` | Renders the book once, into `book/`, then stops.                                                                                                 |
| `make serve` | Renders it and keeps serving it, rebuilding and refreshing the page whenever a file under `src/` changes. This is the one to use while studying. |
| `make clean` | Deletes what those two generate — `book/`, and the Markdown produced from the Lean sources — so the next build starts from nothing.              |

Both `make build` and `make serve` render the Markdown that is already in
`src/`. The chapters are themselves generated from the `.lean` files, so
after editing Lean source run plain `make`, which converts and then builds.
Reach for `make clean` only when a build looks stale or inconsistent;
nothing you wrote is lost, since it removes generated files only.

### Start the server

In the container terminal:

```bash
make serve
```

This runs `mdbook serve -n 0.0.0.0` for you. The `-n 0.0.0.0` matters: left
to its default, mdBook binds only the IPv6 loopback address, while VS
Code's port forwarding reaches the container over IPv4. The browser then
reports `ERR_CONNECTION_REFUSED` even though the server is running and
rebuilding normally. Wait for the line `Serving on: http://0.0.0.0:3000`
before going on.

**Then find the address your own browser should use.** Port 3000 is the port
*inside* the container. VS Code forwards it to a port on your laptop, and
that port is frequently *not* 3000 — it is often a high number such as
`64461`, and it can change from one session to the next. Do not guess it,
and do not assume `http://localhost:3000` will work.

Open the **PORTS** panel — the tab beside TERMINAL — and read the **Local
Address** column on the row labeled **mdBook**. Whatever it says is the
address that works. Right-click that row and choose **Open in Browser**, or
copy the address.

**Then put the book beside the source, not on top of it.** The order of
these steps matters; dragging tabs around is the unreliable way to do it.

1. Open the chapter you are working on, so that a `.lean` file is the
   active editor.
2. From the Command Palette, run **Simple Browser: Show** and paste the
   forwarded address. The browser opens as a tab in the *same* column, so
   it hides the source. That is expected; the next step fixes it.
3. With the Simple Browser tab still focused, run **View: Move Editor into
   Next Group** from the Command Palette. VS Code creates a second column
   on the right and moves the browser into it.
4. Click the `.lean` tab in the left column. Both are now visible at once,
   with no tab switching.

Dragging works too, but only if you drop the tab on the right *edge* of the
editor area, where a vertical highlight appears down the side. Dropped
anywhere else, the tab joins the column it came from and you are back to
flipping between tabs.

The book page for a chapter follows the source path exactly. Editing

    FPCourse/T01_ExpressionsFunctionsRecursion/Week00_AlgebraicTypes.lean

corresponds to

    .../FPCourse/T01_ExpressionsFunctionsRecursion/Week00_AlgebraicTypes.html

in the book, so you can edit the address directly rather than clicking
through the sidebar.

**The Lean infoview competes for the same column.** It also opens beside
the source, so with the book already there you can end up with three narrow
columns and no room to read. Toggle it off while reading and back on while
working a proof: **Lean 4: Toggle Infoview**, or `Ctrl+Shift+Enter`
(`Cmd+Shift+Enter` on macOS).

The server rebuilds and refreshes automatically as files change. Leave it
running while you work. If you stop it, or close the terminal it is running
in, the forwarded address stops serving and the page goes blank instead of
reporting an error.

## 7. Track the course repository

Steps 1 through 6 leave you able to work. This step connects the course
repository to your editor, so that new assignments, corrections, and answers
to other students' questions reach you where you are already working.

**Nothing in this step needs installing.** The container already supplies
both extensions it uses — **GitHub Pull Requests and Issues** and
**GitLens** — exactly as it supplies Lean 4 and the rest of the toolchain.
They are there the moment the container finishes building.

If you open the Extensions view to look for them — the Extensions icon in
the Activity Bar, or `Ctrl+Shift+X` (`Cmd+Shift+X` on a Mac) — find them
under the **Dev Container: CS1** heading rather than **Local**. An extension
installed locally does not run in the container window, which is where you
work, so installing either one by hand would leave you with a copy in the
wrong place and no visible benefit.

### Sign in to GitHub

Click the **GitHub** icon — the Octocat silhouette — in the Activity Bar, the
narrow strip down the left edge. If a **Login** view greets you, click **Sign in** and authorize VS Code
in the browser that opens. The container reuses the account and Git
credentials of the VS Code running on your laptop, so you may instead be
asked only to approve access with a single click, or not asked at all.

Signed in, the GitHub view holds three lists: **Pull Requests**, **Issues**,
and **Notifications**.

The extension reads the repository's `origin` and `upstream` remotes — that
is the default of its `githubPullRequests.remotes` setting — which is why
adding `upstream` back in step 3 matters here.

### Watch the repository

Open the course repository —
**[github.com/kevinsullivan/Lean4CS1](https://github.com/kevinsullivan/Lean4CS1)** — and click **Watch**, at the top
right beside **Fork**. Choose **All Activity**, or **Custom** and tick
**Issues**. GitHub will then email you when something is opened, changed, or
answered.

Watching is the feature that notifies you. *Starring* a repository bookmarks
it on your account and *pinning* displays it on your profile page; neither
sends you anything, and neither changes what VS Code shows you.

### Show course issues in the editor

The Issues view ships with queries about *your* repository and *your* issues.
The course issues are not in your fork: a fork begins with none of the
original's issues, and GitHub leaves the Issues tab switched off on forks by
default. So add a query that names the course repository outright.

Open the Command Palette and run **Preferences: Open User Settings (JSON)**,
then add:

```json
"githubIssues.queries": [
  {
    "label": "Course Issues",
    "query": "repo:kevinsullivan/Lean4CS1 is:open sort:updated-desc"
  },
  {
    "label": "Assigned to Me",
    "query": "repo:kevinsullivan/Lean4CS1 is:open assignee:${user}"
  }
]
```

Each entry becomes a collapsible group in the Issues view. The query text is
ordinary [GitHub search syntax](https://docs.github.com/en/search-github/searching-on-github/searching-issues-and-pull-requests); `${user}` expands to whoever is
signed in. Note that this setting *replaces* the built-in queries rather than
adding to them, so list everything you want to see.

Hovering a query row in the Issues view reveals a pencil, **Edit Query**,
which brings you back to this setting. There is no *Configure Queries* item
in the view's `...` menu or in the Command Palette; the setting is the route.

User settings are reused inside the container, so this survives a container
rebuild. If you would rather the query travel with your fork, put the same
block in `.vscode/settings.json` in the project instead — workspace settings
take precedence over user ones.

The **Notifications** view is a narrower thing than its name suggests: it
reports on pull requests only, and is off until you set
`githubPullRequests.notifications` to `pullRequests`. Email from watching the
repository remains the dependable alert.

### See new upstream commits

VS Code and GitLens show you the remote as of your last `git fetch`. Nothing
streams in on its own, and `git.autofetch` is off by default; even set to
`true` it fetches only the repository's default remote, which is `origin` —
your fork, where course commits never appear. To have `upstream` polled too,
add to the same settings file:

```json
"git.autofetch": "all",
"git.autofetchPeriod": 180
```

The period is in seconds, and 180 is the default.

New commits then show up without your asking. In the **Source Control** side
bar, expand **Remotes → upstream** — that view comes from GitLens, and lives
there rather than in the GitLens side bar, which holds the Commit Graph and
Home. Either will show you what the instructor has pushed.

Fetching only updates what you can *see*. To bring the changes into your own
files, merge them as described under "Working from day to day" below.

## 8. Verify your setup

Work down this list. If every line holds, you are ready.

- VS Code's bottom-left indicator reads **Dev Container: CS1**.
- `lean --version` matches the version in `lean-toolchain`.
- `lake build` finishes without errors.
- Opening a `.lean` file shows the Lean infoview; placing the cursor on a
      `#eval` or `#check` line displays its result.
- `make build` finishes without errors and writes a `book/` directory.
- `make serve` prints `Serving on: http://0.0.0.0:3000`, and the **Local
      Address** shown in the **PORTS** panel opens this book in a browser.
- `git remote -v` lists both `origin` (your fork) and `upstream`.
- The GitHub view's **Issues** list shows the course repository's open
      issues under **Course Issues**.

## Working from day to day

**Save your work.** The container is disposable; your files live in the
cloned folder on your laptop and are safe. Commit and push regularly so your
work also exists on GitHub:

```bash
git add .
git commit -m "Week 3 exercises"
git push origin main
```

**Collect course updates.** When new material is published:

```bash
git fetch upstream
git merge upstream/main
```

If the update changes `lean-toolchain` or `lake-manifest.json`, run
`lake exe cache get` again afterward.

## When something goes wrong

| Symptom                                                         | Likely cause and remedy                                                                                                                                                                                                                                                               |
| --------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| "Cannot connect to the Docker daemon"                           | Docker Desktop is not running. Start it and retry.                                                                                                                                                                                                                                    |
| Container build fails partway                                   | Usually disk or memory. Free space, raise Docker's memory limit, then run **Dev Containers: Rebuild Container**.                                                                                                                                                                      |
| No Lean infoview; no red squiggles                              | The Lean extension has not activated. Open a `.lean` file and wait; if nothing happens, run **Developer: Reload Window**.                                                                                                                                                             |
| `lake: command not found`                                       | The toolchain is not installed yet. Complete step 5, then open a fresh terminal.                                                                                                                                                                                                      |
| Build runs for hours                                            | Mathlib is compiling from source. `Ctrl+C`, then `lake exe cache get`.                                                                                                                                                                                                                |
| `bash\r: command not found`, or scripts failing oddly (Windows) | Files were checked out with CRLF line endings. Apply the Git settings in step 3, then delete the folder and clone again.                                                                                                                                                              |
| "File name too long" or missing files under `.lake` (Windows)   | `core.longpaths` is not set. Run `git config --global core.longpaths true`.                                                                                                                                                                                                           |
| `ERR_CONNECTION_REFUSED` in the browser                         | Most often you used `http://localhost:3000` instead of the **Local Address** from the **PORTS** panel — they are usually different ports. Failing that, mdBook was started without `-n 0.0.0.0` and is listening on IPv6 loopback only; stop it with `Ctrl+C` and rerun `make serve`. |
| The page is completely blank, with no error message at all      | The forward is alive but nothing is answering behind it: mdBook is not running. It was stopped, or the terminal it started in was closed. Rerun `make serve`.                                                                                                                         |
| No **mdBook** row in the **PORTS** panel                        | The forward was never established. Click **Forward a Port** in that panel and enter `3000`, or run `"$BROWSER" http://localhost:3000/` in the container terminal, which asks VS Code to create the forward and open it.                                                               |
| The GitHub view shows only **Login**                            | You are not signed in. Click **Sign in** in that view and authorize VS Code in the browser.                                                                                                                                                                                           |
| The **Issues** list is empty                                    | The query names your fork rather than the course repository. Forks start with no issues and have the Issues tab off by default; use the literal `repo:kevinsullivan/Lean4CS1` shown in step 7.                                                                                        |

Still stuck? Bring the exact command you ran and the exact message you saw —
copy the text rather than describing it — and ask in office hours or by
email.
