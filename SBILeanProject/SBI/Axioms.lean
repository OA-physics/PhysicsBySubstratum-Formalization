import SBILeanProject.SBI.Basic

set_option autoImplicit false

/-
A1 — Relational closure.

The manuscript's A1 contains two logically related clauses:

1. physically meaningful descriptors are invariant under
   relational equivalence;

2. physically meaningful relations possess relational support.

They are packaged here as one physical axiom so that the formal
dependency structure matches the manuscript-level axiomatics.
-/
structure RelationalClosureAxiom
    (Org : Type)
    (RelEq : Org → Org → Prop)
    (PhysMeaningful : {α : Type} → (Org → α) → Prop)
    (RelWitness : Org → Org → Prop) where

  /-
  A1a — invariance under relational equivalence.
  -/
  invariance :
    ∀ {α : Type}
      {F : Org → α}
      {R₁ R₂ : Org},
      PhysMeaningful F →
      RelEq R₁ R₂ →
      F R₁ = F R₂

  /-
  A1b — relational support.

  If a physically meaningful binary relation holds between
  R₁ and R₂, that relation possesses a relational witness.
  -/
  relational_support :
    ∀ {G : Org → Org → Prop}
      {R₁ R₂ : Org},
      PhysMeaningful G →
      G R₁ R₂ →
      RelWitness R₁ R₂


/-
A2 — Local mediation at fixed operational resolution.

The unrestricted relation

    Sigma a p

means that relational participation p belongs to elementary
interaction a without restriction to the operational resolution
currently under consideration.

A2 concerns what that interaction resolves operationally.  The
predicate

    SigmaOp a p

means that p is one of the relational participations distinguished
in a at the operational resolution represented by this formal
development.

Only the structure distinguished at the fixed operational resolution
is required to be finite.  No finiteness or discreteness is imposed
on Sigma a itself or on the substratum as a whole.

The type Alternative a represents the alternatives operationally
distinguished by interaction a at the same resolution.

Finally, local mediation requires a directly mediated pair of
elementary interactions to share an operationally distinguished
relational participation.
-/
structure LocalMediationAxiom
    (Interaction : Type)
    (Participation : Type)
    (Sigma : Interaction → Participation → Prop)
    (MediationStep : Interaction → Interaction → Prop) where

  /-
  Operationally resolved relational participation.

  Manuscript notation:
      p ∈ Sigma_op(a)
  -/
  SigmaOp :
    Interaction → Participation → Prop

  /-
  Every operationally resolved participation is genuinely part
  of the unrestricted interaction.  SigmaOp therefore refines Sigma;
  it does not introduce a second independent interaction structure.
  -/
  sigmaOp_sub_sigma :
    ∀ {a : Interaction} {p : Participation},
      SigmaOp a p →
      Sigma a p

  /-
  Finite operational relational support.

  At the fixed operational resolution under consideration, one
  elementary interaction distinguishes only finitely many relational
  participations.

  The finite List is an explicit enumeration witness.  This says
  nothing about the cardinality of Sigma(a) before operational
  resolution.
  -/
  sigmaOp_finite :
    ∀ a : Interaction,
      ∃ P : List Participation,
        ∀ p : Participation,
          SigmaOp a p →
          p ∈ P

  /-
  Alternatives operationally distinguished by one elementary
  interaction at the same fixed operational resolution.
  -/
  Alternative :
    Interaction → Type

  /-
  Finite operational alternative resolution.

  Every alternative distinguished by one elementary interaction is
  contained in a finite enumeration.  Again, this is a statement about
  operational resolution.  It does not constrain finer or unresolved
  relational structure.
  -/
  alternative_finite :
    ∀ a : Interaction,
      ∃ Ω : List (Alternative a),
        ∀ ω : Alternative a,
          ω ∈ Ω

  /-
  Local mediation.

  If mediation passes directly between elementary interactions a
  and b, the mediation must pass through at least one relational
  participation operationally distinguished in both interactions.

  Manuscript form:

      M(a,b) =>
        exists p,
          p ∈ Sigma_op(a) and p ∈ Sigma_op(b).
  -/
  local_mediation :
    ∀ {a b : Interaction},
      MediationStep a b →
      ∃ p : Participation,
        SigmaOp a p ∧
        SigmaOp b p


/-
A3 — Persistence.

Persistence is deliberately introduced here rather than in SBIBase.

Thus the persistence relation itself, its equivalence properties,
and the existence of at least one nontrivial persistence class are
all parts of A3.

This ensures that downstream use of persistent identity is formally
dependent on A3 rather than on pre-axiomatic vocabulary.
-/
structure PersistenceAxiom
    (Org : Type)
    (RelEq : Org → Org → Prop) where

  /-
  Persistence relation.

  Manuscript notation:
      R₁ ~p R₂
  -/
  Persist : Org → Org → Prop

  /-
  Persistent identity is reflexive, symmetric, and transitive.
  -/
  persist_refl :
    ∀ R, Persist R R

  persist_symm :
    ∀ {R₁ R₂},
      Persist R₁ R₂ →
      Persist R₂ R₁

  persist_trans :
    ∀ {R₁ R₂ R₃},
      Persist R₁ R₂ →
      Persist R₂ R₃ →
      Persist R₁ R₃

  /-
  A3 nontriviality.

  At least one persistent identity admits relationally
  inequivalent realizations.

  Manuscript form:

      ∃ R₁,R₂ ∈ ℛ :
        R₁ ≄rel R₂ ∧ R₁ ~p R₂
  -/
  nontrivial :
    ∃ R₁ R₂ : Org,
      ¬ RelEq R₁ R₂ ∧ Persist R₁ R₂


/-
The admissible SBI framework.

SBIBase supplies only the primitive formal vocabulary.

The three physical admissibility axioms are represented here as:

  A1 : relational closure
  A2 : local mediation
  A3 : persistence
-/
structure SBI extends SBIBase where

  /-
  Relational equivalence is reflexive, symmetric,
  and transitive.

  These properties belong to the definition of relational
  equivalence used by the framework and precede A1 in the
  manuscript development.
  -/
  relEq_refl :
    ∀ R, RelEq R R

  relEq_symm :
    ∀ {R₁ R₂},
      RelEq R₁ R₂ →
      RelEq R₂ R₁

  relEq_trans :
    ∀ {R₁ R₂ R₃},
      RelEq R₁ R₂ →
      RelEq R₂ R₃ →
      RelEq R₁ R₃

  /-
  A1 — Relational closure.

  Both invariance and relational support are contained in
  this single axiom package.
  -/
  A1 :
    RelationalClosureAxiom
      Org
      RelEq
      PhysMeaningful
      RelWitness


  /-
  A2 — Local mediation.

  A2 packages both the finite operational resolution of one
  elementary interaction and the requirement that direct mediation
  proceed through shared operationally resolved participation.
  -/
  A2 :
    LocalMediationAxiom
      Interaction
      Participation
      Sigma
      MediationStep

  /-
  A3 — Persistence.

  The persistence relation, its equivalence structure, and
  its nontriviality condition are all contained in A3.
  -/
  A3 :
    PersistenceAxiom Org RelEq

/-
Operationally resolved participation supplied by A2.

This is the formal counterpart of Sigma_op(a) in Supplementary
Discussion S1.
-/
def SBI.SigmaOp
    (M : SBI)
    (a : M.Interaction)
    (p : M.Participation) : Prop :=
  M.A2.SigmaOp a p


/-
Operational alternatives distinguished by an elementary interaction
at the fixed operational resolution.
-/
def SBI.Alternative
    (M : SBI)
    (a : M.Interaction) : Type :=
  M.A2.Alternative a


/-
Every operationally resolved participation belongs to the underlying
interaction.
-/
theorem SBI.sigmaOp_sub_sigma
    (M : SBI)
    {a : M.Interaction}
    {p : M.Participation}
    (h : M.SigmaOp a p) :
    M.Sigma a p := by
  exact M.A2.sigmaOp_sub_sigma h


/-
A2 supplies a finite enumeration of the relational participations
resolved in each elementary interaction.
-/
theorem SBI.sigmaOp_finite
    (M : SBI)
    (a : M.Interaction) :
    ∃ P : List M.Participation,
      ∀ p : M.Participation,
        M.SigmaOp a p →
        p ∈ P := by
  exact M.A2.sigmaOp_finite a


/-
A2 supplies a finite enumeration of the alternatives distinguished
by each elementary interaction.
-/
theorem SBI.alternative_finite
    (M : SBI)
    (a : M.Interaction) :
    ∃ Ω : List (M.Alternative a),
      ∀ ω : M.Alternative a,
        ω ∈ Ω := by
  exact M.A2.alternative_finite a


/-
Public theorem form of the local-mediation clause of A2.

Downstream proofs use this theorem rather than accessing the packaged
A2 field directly, keeping the formal dependency on A2 explicit and
the proof interface close to the manuscript notation.
-/
theorem SBI.A2_local_mediation
    (M : SBI)
    {a b : M.Interaction}
    (h : M.MediationStep a b) :
    ∃ p : M.Participation,
      M.SigmaOp a p ∧
      M.SigmaOp b p := by
  exact M.A2.local_mediation h

/-!
Compatibility interface

The following definitions and theorems expose the old convenient API
while routing it through the packaged axioms above.

This keeps downstream files readable while ensuring that their formal
dependency on A1, A2, or A3 remains visible.
-/


/-
Persistence relation supplied by A3.

Using `def` rather than placing Persist in SBIBase is intentional:
all downstream persistence statements now pass through A3.
-/
def SBI.Persist
    (M : SBI) :
    M.Org → M.Org → Prop :=
  M.A3.Persist


/-
Convenience wrappers for the equivalence properties of persistence.
These preserve the previous M.persist_refl / symm / trans interface.
-/
theorem SBI.persist_refl
    (M : SBI)
    (R : M.Org) :
    M.Persist R R := by
  exact M.A3.persist_refl R


theorem SBI.persist_symm
    (M : SBI)
    {R₁ R₂ : M.Org}
    (h : M.Persist R₁ R₂) :
    M.Persist R₂ R₁ := by
  exact M.A3.persist_symm h


theorem SBI.persist_trans
    (M : SBI)
    {R₁ R₂ R₃ : M.Org}
    (h₁₂ : M.Persist R₁ R₂)
    (h₂₃ : M.Persist R₂ R₃) :
    M.Persist R₁ R₃ := by
  exact M.A3.persist_trans h₁₂ h₂₃


/-
Explicit theorem exposing the nontriviality clause of A3.
-/
theorem SBI.A3_nontrivial
    (M : SBI) :
    ∃ R₁ R₂ : M.Org,
      ¬ M.RelEq R₁ R₂ ∧
      M.Persist R₁ R₂ := by
  exact M.A3.nontrivial


/-
Convenience wrapper for the invariance clause of A1.
-/
theorem SBI.A1_invariance
    (M : SBI)
    {α : Type}
    {F : M.Org → α}
    {R₁ R₂ : M.Org}
    (hPhys : M.PhysMeaningful F)
    (hRel : M.RelEq R₁ R₂) :
    F R₁ = F R₂ := by
  exact M.A1.invariance hPhys hRel


/-
Compatibility wrapper for the relational-support clause of A1.

Existing downstream uses of

    M.A1_relational_support ...

can therefore remain unchanged.
-/
theorem SBI.A1_relational_support
    (M : SBI)
    {G : M.Org → M.Org → Prop}
    {R₁ R₂ : M.Org}
    (hPhys : M.PhysMeaningful G)
    (hG : G R₁ R₂) :
    M.RelWitness R₁ R₂ := by
  exact M.A1.relational_support hPhys hG


/-
R₁ and R₂ are physically distinguishable when some
physically meaningful descriptor assigns different
values to them.
-/
def SBI.PhysDist
    (M : SBI)
    (R₁ R₂ : M.Org) :
    Prop :=
  ∃ (α : Type) (F : M.Org → α),
    M.PhysMeaningful F ∧
    F R₁ ≠ F R₂


/-
Contrapositive form of the invariance clause of A1.

If some physically meaningful descriptor distinguishes
R₁ and R₂, they cannot be relationally equivalent.
-/
theorem SBI.A1_contrapositive
    (M : SBI)
    {R₁ R₂ : M.Org}
    (hDist : M.PhysDist R₁ R₂) :
    ¬ M.RelEq R₁ R₂ := by

  rcases hDist with ⟨α, F, hPhys, hDiff⟩

  intro hRel

  have hSame : F R₁ = F R₂ :=
    M.A1.invariance hPhys hRel

  exact hDiff hSame
