# Formal verification of *The Structure of Time*

This directory documents the Lean formalization accompanying the manuscript
*The Structure of Time*.

The formal Lean development is located in:

`SBILeanProject/Time/`

The manuscript-level Lean entry point is:

`SBILeanProject/Time.lean`

The Time formalization imports previously verified structural results from the
SBI formalization in:

`SBILeanProject/SBI/`

The purpose of this documentation is to let a reader inspect the formal
verification relevant to the Time manuscript without first having to study the
entire SBI development.

## Verification and traceability documentation

NASA-style verification and manuscript-to-Lean traceability documentation is
available at the repository root:

- `Time_Formal_Verification_Traceability_Matrix.md` — statement-by-statement
  verification matrix, semantic-fidelity notes, completeness audit, and
  configuration-control guidance.
- `Time_S1_Lean_Traceability_v1.txt` — compact S1-to-Lean manuscript-facing
  interface registry.

The generated dependency reports provide the machine-derived audit layer beneath
these documents, including the declaration-level manuscript map, grouped map,
and SBI-boundary report.

