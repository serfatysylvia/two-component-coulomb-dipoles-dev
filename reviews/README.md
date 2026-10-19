# Reviews

Two independent reviews were carried out before publication, on release candidates of this
repository (the candidates themselves were not published). Each reviewer worked refute-first,
had not written or edited the material under review, and edited nothing.

| Report | Scope | Candidate reviewed |
|---|---|---|
| `statement_audit.md` | Every frozen statement and definition in `TwoComponentCoulomb/Frozen/` against the pinned source and `RULINGS.md`: binders, quantifier order, constants, conventions, hypothesis smuggling, provider consumption, axioms | `c553d18` |
| `release_review.md` | The release itself: private material, scope, preservation of the author-approved statements, a clean-checkout build, documentation and citation accuracy, licensing, CI | `14d049f` (final) |

The statement audit found no defect (PASS, cosmetic notes only). Its two docstring notes were
applied afterwards. The later candidates changed documentation and proofs only: the 32 frozen
declarations of the published tree have exactly the elaborated forms audited in
`statement_audit.md` (their `abi_sha256` values in `manifest/frozen_anchors.json` are
unchanged). The release review lists its findings on the first candidate and their resolution. The
published tree differs from the final reviewed candidate `14d049f` only by this directory, by the
changes the release review suggested (the comment corrections N1 and N2 and the attribution note
N3), and by the authors' decisions at publication (they approved ruling R21 and named the copyright
holders).
