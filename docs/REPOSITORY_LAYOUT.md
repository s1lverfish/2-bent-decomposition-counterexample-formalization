# Repository packaging

The layout follows Lean research projects such as [PFR](https://github.com/teorth/pfr) and [sphere eversion](https://github.com/leanprover-community/sphere-eversion): a root library import, a source directory, pinned `lean-toolchain`/Lake dependency files, VS Code extension recommendations, mathematical documentation, and GitHub CI. Downloaded libraries, caches, binaries, unrelated research notes and manuscript drafts are excluded. A large blueprint website is unnecessary for this small development; PAPER_MAP.md gives the theorem-to-source correspondence.

CI uses the official [Lean action](https://github.com/leanprover/lean-action). It builds the library, then runs the explicit admission/axiom audit. Dependencies are pinned in the committed manifest rather than copied into the repository.
