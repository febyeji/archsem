# Repository Instructions

## VCS

- This repository is managed with jj; use jj when `jj status` works.
- Before editing in a shared checkout, report `jj status`, `jj log -r @ -n 1`,
  and `jj bookmark list`, then state the intended base, owned bookmark, and
  file scope.
- Each task should have one owned bookmark. Do not move, squash, rebase,
  describe, or push another task's bookmark.
- Before `jj rebase`, `jj squash`, `jj bookmark set`, `jj describe`, or
  `jj git push`, re-check bookmark tips and show the exact stack order. If a
  tip changed unexpectedly, stop and ask.
- Push only explicit bookmarks; avoid broad push commands in multi-agent work.

## JJ Workspaces

- Extra jj workspaces for this repo should live under the persistent worktree
  directory `/Volumes/Codespaces/_worktrees/archsem/<workspace-name>`.
- Use `jj workspace add --name <workspace-name>
  /Volumes/Codespaces/_worktrees/archsem/<workspace-name> -r <base>` so the
  folder basename, workspace name, and task/bookmark name line up.
- Use `jj workspace list` to find all tracked workspaces later. The durable
  handles are the jj workspace name, bookmark name, commit graph, and the
  worktree directory.
- When handing work off to another agent or thread, report the workspace path,
  workspace name, base revision, owned bookmark, and file scope.

## Builds And Checks

- Follow `STYLE.md` for Rocq/Coq style. Do not mix style-only churn with
  semantic changes.
- Prefer narrow validation targets. For Coq changes, usually run the relevant
  `dune build` target through the repo-local opam switch, e.g.
  `opam exec --switch=/Volumes/Codespaces/rems-project/archsem -- dune build
  --root . -j 1 <target>`.

## Cambridge Remote Access

- Obtain a forwardable Kerberos ticket before connecting:
  `kinit -f yh590@DC.CL.CAM.AC.UK`.
- Connect to the Ely host with Kerberos credential forwarding:
  `ssh -K yh590@ely.cl.cam.ac.uk`.
- Verify the remote repository path and working-tree state before replacing or
  synchronizing an `archsem` checkout.

## Commits

- Match the existing scoped style: `feat(Isla): ...`, `fix(VMPromising): ...`,
  `fix(arm): ...`, `chore(arm): ...`.
- Use a capitalized imperative subject after the scope, such as `Support`,
  `Keep`, `Parse`, `Handle`, or `Update`.
- Keep one logical PR/change per commit. ArchSem squash-merges PRs, so the
  final commit message should summarize the user-visible change.
- Include a concise body when validation evidence, semantic scope, or proof/test
  limits matter. Keep rationale and tradeoffs in the user-facing explanation.
