# Reviews

Two independent reviews were carried out before publication, on release candidates of this
repository (the candidates themselves were not published). A third compares the frozen
statements with the current source.
Each reviewer worked refute-first, had not written or edited the material under review, and
edited nothing.

The first two reports refer to the revision of 2026-10-18, SHA-256
`2c6fc7b48ee7e9c0e4e8bb9591e513edba49ece4ce6c54bb493c4026147726f6`. Their line numbers and declaration names refer to that
revision. Those reports are retained exactly as written. The third report compares the
frozen statements with the current source and finds that all 32 match.

| Report | Scope | Candidate reviewed |
|---|---|---|
| `statement_audit.md` | Every frozen statement and definition in `TwoComponentCoulomb/Frozen/` against the pinned source and `RULINGS.md`: binders, quantifier order, constants, conventions, hypothesis smuggling, provider consumption, axioms | `c553d18` |
| `release_review.md` | The release itself: private material, scope, preservation of the author-approved statements, a clean-checkout build, documentation and citation accuracy, licensing, CI | `14d049f` (final) |
| `statement_audit_2026-10-22.md` | All 32 frozen declarations against the current `source/dipole-formation.tex`, including the joint upper bound of Propositions 3.9 and 3.10 | Current source |

The statement audit found no defect (PASS, cosmetic notes only). Its two docstring notes were
applied afterwards. The later candidates changed documentation and proofs only: the 32 frozen
declarations of the final candidate `14d049f` have exactly the elaborated forms audited in
`statement_audit.md` (their `abi_sha256` values in `manifest/frozen_anchors.json` are
unchanged). The release review lists its findings on the first candidate and their resolution.
Later changes to the proofs leave the elaborated frozen statements unchanged, up to the renames
recorded in R24.
