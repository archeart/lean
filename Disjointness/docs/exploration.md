# Exploring the Lean project

The installed setup consists of Zed's Lean 4 extension, doc-gen4, LeanArchitect,
leanblueprint, and Graphviz. The Lean toolchain remains v4.35.0-rc4, and the
mathematical dependency revisions from the original lockfile are preserved.

## Open the explorer

Run these commands from the `Disjointness` directory:

```sh
./scripts/explore open
```

This starts a background server bound to `127.0.0.1` and opens
<http://127.0.0.1:8000/>. The landing page links to:

- API documentation for the project and imported libraries;
- declaration search;
- the mathematical blueprint;
- its interactive dependency graph.

Source links in the API docs open local Lean source as text in the browser.
Use Zed's definition navigation when you want to inspect the same code in the
editor. The blueprint's Lean links lead into the generated API docs.

For a foreground server that stops with Ctrl-C, use:

```sh
./scripts/explore serve
```

Both `open` and `serve` accept `--port 8001` if port 8000 is occupied.
When `open` starts a background server, its PID and log are in `.explore/`.

## Zed

Open the **Disjointness directory**, which contains `lakefile.toml` and
`lean-toolchain`, as the project. The Lean 4 extension uses the existing elan/Lake
installation; no new default Lean toolchain is needed. Semantic highlighting is
enabled by this project's `.zed/settings.json`.

The command palette's `task: spawn` offers:

- `Lean: check project`
- `Lean: build API docs`
- `Lean: build blueprint`
- `Lean: open explorer`

The extension supports ordinary language-server features and Unicode snippets.
It currently lacks the integrated Lean Infoview. A blueprint gives the proof's
overall structure; it does not display the live tactic goals.

Your existing user settings were preserved. Before enabling Lean auto-install,
a backup was saved at `~/.config/zed/settings.before-lean-2026-10-14.json`.

## Rebuild documentation

```sh
./scripts/explore docs        # API documentation and local source links
./scripts/explore blueprint   # LeanArchitect extraction, website, declaration check
./scripts/explore build       # both
```

The first API build indexes Lean and the transitive mathlib/PFR imports and is
substantially longer than subsequent builds. Generated files are ignored by Git.

doc-gen4 is pinned to its v4.35.0-rc4 release commit
`fd5ce8f50b90096067f4e5d867611b585e951dbb` in `docbuild/lakefile.toml`.
Its separate Lake manifest shares the existing dependency checkouts in
`.lake/packages` and records its additional documentation dependencies.

LeanArchitect is pinned to `f45833e26c68aa947044145184f8881a75392e30` in the main
Lake configuration. Its source names rc3, but this pinned revision was built
successfully with this project's rc4 toolchain. Existing batteries and Cli
revisions are explicit requirements so adding the tool does not downgrade them.

Blueprint annotations are collected in `Blueprint.lean`, which imports the
mathematical development and attaches metadata to selected existing declarations.
This keeps documentation edits separate from proof files. `Blueprint` is a
separate library, outside the default mathematical build target. The generated
LaTeX and JSON are in `.lake/build/blueprint/`.

The website source is in `blueprint/src/`. Its graph includes the checked
protocol foundations, complete information argument, actual embeddings, finite
endpoint, and random-tape normalization. The proof correspondence is in
`docs/blueprint.md`. `Disjointness.finiteLowerBoundClaim` now proves the target
proposition defined as `FiniteLowerBoundClaim`.

## Python and Graphviz installation

The blueprint environment is local to this workspace at `../.tools/blueprint`.
It contains Python 3.12, Graphviz 14.1.2, PyGraphviz 2.0.3, and leanblueprint 0.0.20.
The setup did not change system Python or install Homebrew. The helper command
sets the needed executable paths automatically.

`blueprint/environment.yml` records the environment specification. To recreate it
with an existing micromamba installation, run from this project directory:

```sh
micromamba create -y -p "$PWD/../.tools/blueprint" -f blueprint/environment.yml
```

The leanblueprint command-line client assumes a Lake project at the Git repository
root; this project is a subdirectory. `scripts/explore blueprint` therefore runs
the package's documented plasTeX plugin directly, then runs `checkdecls` through
Lake. No upstream package sources are patched. The configured output is the web
blueprint; PDF generation has not been configured.

## Upstream documentation

- [Zed Lean extension](https://github.com/owlx56/zed-lean4)
- [doc-gen4](https://github.com/leanprover/doc-gen4)
- [LeanArchitect](https://github.com/hanwenzhu/LeanArchitect)
- [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
