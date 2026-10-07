# Physics by Substratum — Lean 4 formalization

This repository contains the publication-facing Lean 4 formalization supporting the **Physics by Substratum** research programme.

The present formal development covers three connected parts of the programme:

- **Axiomatic relational structure** — the formal core associated with *An Axiomatic Structure of Relational Physics*
- **Time and duration** — the formal structure associated with *The Structure of Time*
- **Spacetime / GR consequences** — the formal structure associated with *The Structure of Spacetime*

The companion Schrödinger manuscript is not represented by a separate Lean development because its main argument is a physical reconstruction using established mathematical results rather than a chain of new formal propositions of the kind checked here.

The repository is intended to make the deductive structure inspectable independently of the prose manuscripts. The Lean development checks deductions made from the encoded assumptions. It does **not** establish the physical truth of the assumptions, and it does not by itself establish that a chosen formal encoding is the unique physical interpretation of a conceptual statement. The traceability documents therefore distinguish physical axioms, semantic encodings, definitions, derived results, and machine-checked proofs.

## Repository structure

```text
SBILeanProject/
  SBI/       axiomatic relational framework
  Time/      record formation, temporal order, reversible duration
  GR/        spacetime and GR-related consequences

docs/
  SBI/       human-readable formalization notes
  Time/      dependency maps and notes
  GR/        dependency maps and notes
```

Root-level verification and traceability files connect manuscript-facing claims to Lean declarations and source files.

## Build

The project uses Lean 4 and Mathlib. The Lean toolchain and dependency revisions are pinned in `lean-toolchain` and `lake-manifest.json`.

From a clean checkout:

```bash
lake update
lake build
lake build SBILeanProject.SBI.DependencyReport
lake build SBILeanProject.Time.DependencyReport
lake build SBILeanProject.GR.DependencyReport
```

The GitHub Actions workflow performs the publication-facing verification build on every push and pull request.

## Formalization scope

The formalization is deliberately explicit about its scope. In particular:

- Lean verifies implications between the formal statements supplied to it
- physical assumptions remain physical assumptions
- semantic bridges between manuscript concepts and formal objects are documented separately
- coarse-grained or representation-dependent assumptions are not promoted to fundamental axioms merely because they are needed downstream

The verification matrices should be read together with the Lean source when assessing correspondence between a manuscript claim and its formal counterpart.

## Citation and archived snapshot

Version **1.0.0** is archived in Zenodo with DOI **10.5281/zenodo.23205220**. A `CITATION.cff` file is included with the corresponding citation metadata.

## License

This repository uses split licensing appropriate to its mixed software and scientific-documentation content:

- **Lean source code and software/build/CI configuration** are licensed under the **MIT License**; see `LICENSE`.
- **Documentation, traceability matrices, explanatory notes, and manuscript-facing dependency-map documentation** are licensed under the **Creative Commons Attribution 4.0 International License (CC BY 4.0)**; see `LICENSE-DOCUMENTATION`.

The licences govern the copyrighted expression contained in this repository. They do not by themselves determine ownership of the underlying physical ideas, mathematical propositions, or scientific claims.
