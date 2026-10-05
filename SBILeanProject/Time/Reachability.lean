import SBILeanProject.Time.Basic

set_option autoImplicit false

namespace SBI.Time

/-
Operational reversible equivalence.

Two configurations X and Y belong to the same reversible sector when each
is operationally reachable from the other.

Manuscript notation:

    X ~R Y

defined by

    X ≼ Y  and  Y ≼ X.

This is stronger than merely saying that X and Y are connected by some
admissible deformation.  Both directions must be operationally accessible.

The physical meaning is important for the Time manuscript:

* motion within one ~R class can represent extensive reversible evolution;

* no irreversible precedence has yet been established between members of
  the same class;

* irreversible temporal order will arise only when operational reachability
  becomes asymmetric between different reversible classes.
-/
def ReversibleEquivalent
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    (X Y : Configuration K O) : Prop :=

  OperationalReachability D A O X Y ∧
  OperationalReachability D A O Y X


/-
Reversible equivalence is reflexive.

Every configuration is operationally reachable from itself by the zero-step
path, so it is reversibly equivalent to itself.
-/
theorem reversibleEquivalent_refl
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    (X : Configuration K O) :

    ReversibleEquivalent D A O X X := by

  constructor

  · exact operationalReachability_refl D A O X

  · exact operationalReachability_refl D A O X


/-
Reversible equivalence is symmetric.

If X can reach Y operationally and Y can reach X operationally, exchanging
the two configurations simply exchanges the two reachability statements.
-/
theorem reversibleEquivalent_symm
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    {X Y : Configuration K O}
    (hXY :
      ReversibleEquivalent D A O X Y) :

    ReversibleEquivalent D A O Y X := by

  exact ⟨hXY.2, hXY.1⟩


/-
Reversible equivalence is transitive.

Suppose

    X ~R Y

and

    Y ~R Z.

Then operational reachability gives

    X ≼ Y ≼ Z

and therefore

    X ≼ Z.

The reverse paths similarly give

    Z ≼ Y ≼ X

and therefore

    Z ≼ X.

Hence X ~R Z.
-/
theorem reversibleEquivalent_trans
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    {X Y Z : Configuration K O}
    (hXY :
      ReversibleEquivalent D A O X Y)
    (hYZ :
      ReversibleEquivalent D A O Y Z) :

    ReversibleEquivalent D A O X Z := by

  constructor

  · exact
      operationalReachability_trans
        D A O
        hXY.1
        hYZ.1

  · exact
      operationalReachability_trans
        D A O
        hYZ.2
        hXY.2


/-
The preceding three theorems establish that ~R is an equivalence relation.

We package that result as a Lean Setoid.

A Setoid is simply a type together with an explicitly specified equivalence
relation.  This allows Lean's Quotient construction to identify all
configurations belonging to the same operationally reversible class.

No physical assumption is introduced here.  The Setoid merely packages
properties already proved above.
-/
def reversibleSetoid
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M) :
    Setoid (Configuration K O) where

  r :=
    ReversibleEquivalent D A O

  iseqv :=
    {
      refl :=
        reversibleEquivalent_refl D A O

      symm :=
        fun h =>
          reversibleEquivalent_symm D A O h

      trans :=
        fun hXY hYZ =>
          reversibleEquivalent_trans D A O hXY hYZ
    }


/-
Operationally reversible equivalence class.

The quotient identifies configurations whenever they are mutually
operationally reachable.

Manuscript notation:

    [X]R.

An element of ReversibleClass is therefore not one microscopic
configuration.  It represents the entire collection of configurations
connected by mutually accessible reversible rearrangements.

This quotient is crucial for the temporal construction.  Reversible
evolution inside one class is deliberately removed from the later
irreversible ordering relation.
-/
abbrev ReversibleClass
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M) :=

  Quotient (reversibleSetoid D A O)


/-
Canonical reversible class containing configuration X.

Manuscript notation:

    X ↦ [X]R.
-/
def reversibleClassOf
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    (X : Configuration K O) :

    ReversibleClass D A O :=

  Quotient.mk
    (reversibleSetoid D A O)
    X

/-
Asymmetric operational reachability.

This is the configuration-level relation underlying irreversible
precedence.

AsymmetricReachability D A O X Y means

    X ≼ Y

but

    Y ≰ X.

At this stage this is not yet called temporal precedence, because X and Y
are individual configurations rather than operationally reversible
equivalence classes.

Nor do we yet assert that such asymmetry is produced by record formation.
That connection will be proved later from the persistent-record theorem.

This definition isolates the purely order-theoretic structure needed for
the quotient construction.
-/
def AsymmetricReachability
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    (X Y : Configuration K O) : Prop :=

  OperationalReachability D A O X Y ∧
  ¬ OperationalReachability D A O Y X


/-
Asymmetric operational reachability excludes reversible equivalence.

If

    X ≼ Y

but

    Y ≰ X,

then X and Y cannot satisfy the mutual reachability condition defining

    X ~R Y.
-/
theorem asymmetricReachability_not_reversibleEquivalent
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    {X Y : Configuration K O}
    (hXY :
      AsymmetricReachability D A O X Y) :

    ¬ ReversibleEquivalent D A O X Y := by

  intro hEq

  exact hXY.2 hEq.2


/-
Representative independence, forward direction.

Suppose

    X ~R X'
    Y ~R Y'

and asymmetric operational reachability holds from X to Y:

    X ≼ Y
    Y ≰ X.

Then the same asymmetry holds from X' to Y':

    X' ≼ Y'
    Y' ≰ X'.

This is the substantive step required before irreversible precedence can
be defined on quotient classes [X]R and [Y]R.

The proof uses only:

  • mutual operational reachability within each reversible class;
  • transitivity of operational reachability.

No record-formation assumption enters here.
-/
theorem asymmetricReachability_of_representatives
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    {X X' Y Y' : Configuration K O}
    (hXX' :
      ReversibleEquivalent D A O X X')
    (hYY' :
      ReversibleEquivalent D A O Y Y')
    (hXY :
      AsymmetricReachability D A O X Y) :

    AsymmetricReachability D A O X' Y' := by

  constructor

  · /-
    Since X' ~R X, we have X' ≼ X.
    Since Y ~R Y', we have Y ≼ Y'.

    Therefore

        X' ≼ X ≼ Y ≼ Y'.
    -/

    have hX'Y :
        OperationalReachability D A O X' Y :=
      operationalReachability_trans
        D A O
        hXX'.2
        hXY.1

    exact
      operationalReachability_trans
        D A O
        hX'Y
        hYY'.1

  · /-
    Suppose instead that Y' ≼ X'.

    Since Y ≼ Y' and X' ≼ X, transitivity would give

        Y ≼ Y' ≼ X' ≼ X,

    hence Y ≼ X, contradicting the assumed asymmetry.
    -/

    intro hY'X'

    have hYX' :
        OperationalReachability D A O Y X' :=
      operationalReachability_trans
        D A O
        hYY'.1
        hY'X'

    have hYX :
        OperationalReachability D A O Y X :=
      operationalReachability_trans
        D A O
        hYX'
        hXX'.2

    exact hXY.2 hYX


/-
Full representative independence.

Replacing either representative by any reversibly equivalent
configuration preserves asymmetric operational reachability.

Thus

    X ~R X'
    Y ~R Y'

implies

    (X ≼ Y and Y ≰ X)
        ↔
    (X' ≼ Y' and Y' ≰ X').

This is the exact mathematical content required for the manuscript's
Representative Independence lemma.
-/
theorem asymmetricReachability_iff_of_reversibleEquivalent
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    {X X' Y Y' : Configuration K O}
    (hXX' :
      ReversibleEquivalent D A O X X')
    (hYY' :
      ReversibleEquivalent D A O Y Y') :

    AsymmetricReachability D A O X Y ↔
    AsymmetricReachability D A O X' Y' := by

  constructor

  · intro hXY

    exact
      asymmetricReachability_of_representatives
        D A O
        hXX'
        hYY'
        hXY

  · intro hX'Y'

    exact
      asymmetricReachability_of_representatives
        D A O
        (reversibleEquivalent_symm D A O hXX')
        (reversibleEquivalent_symm D A O hYY')
        hX'Y'

/-
Asymmetric operational reachability is transitive.

Suppose

    X ≼ Y,   Y ≰ X

and

    Y ≼ Z,   Z ≰ Y.

Then transitivity of operational reachability gives

    X ≼ Z.

If Z ≼ X also held, then

    Z ≼ X ≼ Y,

which would imply Z ≼ Y and contradict the second asymmetry.

Thus

    X ≺ Z

at the configuration level.

This is the order-theoretic core of transitivity of irreversible
precedence.
-/
theorem asymmetricReachability_trans
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    {X Y Z : Configuration K O}
    (hXY :
      AsymmetricReachability D A O X Y)
    (hYZ :
      AsymmetricReachability D A O Y Z) :

    AsymmetricReachability D A O X Z := by

  constructor

  · exact
      operationalReachability_trans
        D A O
        hXY.1
        hYZ.1

  · intro hZX

    have hZY :
        OperationalReachability D A O Z Y :=
      operationalReachability_trans
        D A O
        hZX
        hXY.1

    exact hYZ.2 hZY
/-
Irreversible precedence on operationally reversible equivalence classes.

The relation is defined by asymmetric operational reachability between
representatives:

    [X]R ≺ [Y]R

when

    X ≼ Y

but

    Y ≰ X.

The preceding representative-independence theorem guarantees that the
truth of this statement does not depend on which representatives X and Y
are chosen from their reversible classes.

This is the manuscript's irreversible precedence relation.
-/
def IrreversiblePrecedence
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M) :
    ReversibleClass D A O →
    ReversibleClass D A O →
    Prop :=

  fun q₁ q₂ =>
    Quotient.liftOn₂
      q₁
      q₂
      (fun X Y =>
        AsymmetricReachability D A O X Y)
      (by
        intro X X' Y Y' hXX' hYY'

        exact
          propext
            (asymmetricReachability_iff_of_reversibleEquivalent
              D A O
              hXX'
              hYY'))
/-
For explicit representatives X and Y, irreversible precedence between
their quotient classes is exactly asymmetric operational reachability
between X and Y.

This theorem connects the quotient-level manuscript notation

    [X]R ≺ [Y]R

to the configuration-level condition

    X ≼ Y  and  Y ≰ X.
-/
theorem irreversiblePrecedence_classOf_iff
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    (X Y : Configuration K O) :

    IrreversiblePrecedence D A O
      (reversibleClassOf D A O X)
      (reversibleClassOf D A O Y)
    ↔
    AsymmetricReachability D A O X Y := by

  rfl

/-
Irreversible precedence is irreflexive.

No reversible class can precede itself.

For any representative X, self-precedence would require both

    X ≼ X

and

    X ≰ X.

But operational reachability is reflexive, so these conditions are
incompatible.
-/
theorem irreversiblePrecedence_irrefl
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    (q : ReversibleClass D A O) :

    ¬ IrreversiblePrecedence D A O q q := by

  refine Quotient.inductionOn q ?_

  intro X
  intro hXX

  exact
    hXX.2
      (operationalReachability_refl D A O X)

/-
Irreversible precedence is transitive.

If

    [X]R ≺ [Y]R

and

    [Y]R ≺ [Z]R,

then

    [X]R ≺ [Z]R.

The proof reduces the quotient classes to representatives and applies
transitivity of asymmetric operational reachability proved above.
-/
theorem irreversiblePrecedence_trans
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M)
    {q₁ q₂ q₃ : ReversibleClass D A O}
    (h₁₂ :
      IrreversiblePrecedence D A O q₁ q₂)
    (h₂₃ :
      IrreversiblePrecedence D A O q₂ q₃) :

    IrreversiblePrecedence D A O q₁ q₃ := by

  refine Quotient.inductionOn₃ q₁ q₂ q₃ ?_ h₁₂ h₂₃

  intro X Y Z
  intro hXY hYZ

  exact
    asymmetricReachability_trans
      D A O
      hXY
      hYZ

      
end SBI.Time
