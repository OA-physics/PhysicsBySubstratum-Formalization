# Formal verification of *The Structure of Spacetime*

This directory documents the Lean formalization accompanying the manuscript
*The Structure of Spacetime — An Axiomatic Approach*.

The formal Lean development is located in:

`SBILeanProject/GR/`

The manuscript-level Lean entry point is:

`SBILeanProject/GR.lean`

The GR formalization imports previously verified structural results from:

- `SBILeanProject/SBI/`
- `SBILeanProject/Time/`

The purpose of this documentation is to let a reader inspect the formal
verification relevant to the GR manuscript without first having to reconstruct
the complete SBI and Time developments.

## Verification and traceability documentation

NASA-style verification and manuscript-to-Lean traceability documentation is
available at the repository root:

- `GR_Formal_Verification_Traceability_Matrix.md` — detailed verification
  matrix, semantic-fidelity audit, forward/reverse traceability, scope
  exclusions, and configuration-control guidance.
- `GR_Main_Lean_Traceability_v1.txt` — compact main-manuscript-to-Lean
  interface registry.

The human-facing dependency architecture is described in:

- `docs/GR/GR_Top_Level_Dependency_Map.md` — interpretation of the generated
  grouped proof map, group-to-manuscript anchors, logical-status conventions,
  and reproduction commands.

## Machine-derived dependency reports

The authoritative dependency topology is generated from the checked Lean
declarations. It is not maintained independently by hand.

Relevant generators are:

- `SBILeanProject/GR/DependencyReport.lean` — declaration-level forensic audit,
  manuscript spine, grouped audit, and upstream-boundary reporting;
- `SBILeanProject/GR/RefinedGroupedReport.lean` — refined manuscript-facing
  conceptual grouping while preserving machine-derived edges;
- `SBILeanProject/GR/ColoredDependencyReport.lean` — presentation styling for
  the refined grouped GraphML map.

Recommended verification commands:

```text
lake build SBILeanProject.GR
lake build SBILeanProject.GR.DependencyReport
lake build SBILeanProject.GR.ColoredDependencyReport
```

The final command regenerates the refined grouped map and applies the manuscript
color convention.

## Verification scope

A clean Lean build establishes deductive correctness of the encoded formal
statements. It does not by itself establish the physical adequacy of explicit
coarse-graining bridges, the truth of the imported physical framework, or the
physical identification of a limiting reachability configuration with a
black-hole horizon.

The GR documentation therefore keeps separate:

1. imported SBI/Time results;
2. explicit physical/effective semantic bridges;
3. imported Lorentz and Lovelock mathematics;
4. derived Lean conclusions; and
5. manuscript-level physical interpretations and conjectures outside the
   present theorem layer.

That logical-status separation is part of the verification claim rather than a
qualification added after formalization.