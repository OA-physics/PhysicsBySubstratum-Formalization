import Mathlib.Data.Real.Basic
import Mathlib.Order.CountableDenseLinearOrder
import SBILeanProject.Time.Reachability

set_option autoImplicit false

namespace SBI.Time

/-
Strict partial order of irreversible precedence.

Reachability.lean established separately that irreversible precedence on
operationally reversible equivalence classes is

  • irreflexive, and
  • transitive.

Those two properties are exactly the defining properties of a strict
partial order.

This theorem packages the two previously proved results into the form used
in the Time manuscript.

No additional physical or mathematical assumption enters here.
-/
theorem irreversiblePrecedence_strictPartialOrder
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M) :

    (∀ q : ReversibleClass D A O,
      ¬ IrreversiblePrecedence D A O q q)
    ∧
    (∀ {q₁ q₂ q₃ : ReversibleClass D A O},
      IrreversiblePrecedence D A O q₁ q₂ →
      IrreversiblePrecedence D A O q₂ q₃ →
      IrreversiblePrecedence D A O q₁ q₃) := by

  constructor

  · intro q
    exact irreversiblePrecedence_irrefl D A O q

  · intro q₁ q₂ q₃ h₁₂ h₂₃
    exact
      irreversiblePrecedence_trans
        D A O
        h₁₂
        h₂₃

/-
Ordered physical history.

The Time manuscript does not require irreversible precedence to give a
global total ordering of all reversible equivalence classes.  The relation

    IrreversiblePrecedence D A O

is only a strict partial order.

An ordered physical history is therefore represented as a selected
collection of reversible classes with the additional property that any two
distinct members of that collection are comparable by irreversible
precedence.

Manuscript definition:

    H ⊆ C(S) / ~R

is an ordered physical history when, for any distinct

    [X]R, [Y]R ∈ H,

either

    [X]R ≺ [Y]R

or

    [Y]R ≺ [X]R.

The predicate `member` specifies which reversible classes belong to the
history.  The field `comparable` expresses exactly the chain condition.

No global total ordering is introduced.
-/
structure OrderedPhysicalHistory
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    (D : ConfigurationChangeSemantics K)
    (A : OperationalAccessibilitySemantics D)
    (O : Observer M) where

  /-
  Membership in the physical history.

  Manuscript notation:

      q ∈ H.
  -/
  member :
    ReversibleClass D A O → Prop

  /-
  Chain condition.

  Any two distinct reversible classes belonging to the same ordered
  physical history possess irreversible precedence in one direction
  or the other.
  -/
  comparable :
    ∀ {q₁ q₂ : ReversibleClass D A O},
      member q₁ →
      member q₂ →
      q₁ ≠ q₂ →
      IrreversiblePrecedence D A O q₁ q₂ ∨
      IrreversiblePrecedence D A O q₂ q₁


/-
An element of an ordered physical history.

This subtype consists of a reversible class together with a proof that
the class belongs to H.

It is useful downstream because the scalar temporal representation will
be a function whose domain is the history itself rather than the entire
quotient space.
-/
abbrev HistoryElement
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    (H : OrderedPhysicalHistory D A O) :=

  {q : ReversibleClass D A O // H.member q}

/-
At-most-countable ordered physical history.

The Time manuscript later constructs a scalar temporal coordinate for
ordered physical histories that are finite or countable.

Mathematically, "finite or countable" can be expressed uniformly by saying
that the elements of the history admit an injective encoding into the
natural numbers.

Thus H is at most countable when there exists a map

    encode : HistoryElement H → Nat

such that distinct history elements receive distinct natural numbers.

Finite histories are included automatically.

This condition concerns only the cardinality of the history.  It does not
yet impose any relation between the enumeration and irreversible
precedence.
-/
def HistoryAtMostCountable
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    (H : OrderedPhysicalHistory D A O) : Prop :=

  ∃ encode : HistoryElement H → Nat,
    Function.Injective encode

/-
Irreversible precedence restricted to one ordered physical history.

A `HistoryElement H` contains

  • a reversible equivalence class, and
  • a proof that this class belongs to H.

The history-level relation therefore simply applies the already defined
irreversible precedence relation to the underlying reversible classes.

No new ordering relation is being postulated here.  This is only the
restriction of irreversible precedence to the selected history.
-/
def HistoryPrecedence
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    (H : OrderedPhysicalHistory D A O) :
    HistoryElement H →
    HistoryElement H →
    Prop :=

  fun x y =>
    IrreversiblePrecedence D A O x.1 y.1


/-
On an ordered physical history, irreversible precedence is a strict total
order.

Globally, irreversible precedence is only a strict partial order.  The
additional totality here comes entirely from the defining chain condition
of `OrderedPhysicalHistory`.

The three required properties are:

  • irreflexivity:
      no history element precedes itself;

  • transitivity:
      x ≺ y and y ≺ z imply x ≺ z;

  • trichotomy:
      for any x and y in the history, either
          x ≺ y,
          x = y,
      or
          y ≺ x.

The first two were already proved for irreversible precedence in
Reachability.lean.  Trichotomy follows from the chain condition defining
the ordered physical history.
-/
theorem historyPrecedence_isStrictTotalOrder
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    (H : OrderedPhysicalHistory D A O) :
    IsStrictTotalOrder
      (HistoryElement H)
      (HistoryPrecedence H) where

  toTrichotomous :=
    Std.trichotomous_of_rel_or_eq_or_rel_swap fun {x y} => by

      by_cases hxy : x = y

      · exact Or.inr (Or.inl hxy)

      · have hval : x.1 ≠ y.1 := by
          intro h
          apply hxy
          exact Subtype.ext h

        rcases H.comparable x.2 y.2 hval with hForward | hBackward

        · exact Or.inl hForward

        · exact Or.inr (Or.inr hBackward)

  irrefl x :=
    irreversiblePrecedence_irrefl D A O x.1

  trans x y z hxy hyz :=
    irreversiblePrecedence_trans D A O hxy hyz

/-
Countability of the elements of an ordered physical history.

`HistoryAtMostCountable H` was defined directly in manuscript terms:
there exists an injective encoding of the history elements into the
natural numbers.

Mathlib expresses the same cardinality condition by the typeclass

    Countable (HistoryElement H).

Since the natural numbers are countable, an injective map

    HistoryElement H → Nat

is sufficient to obtain the Mathlib countability structure.

This theorem is therefore only a translation between two equivalent
formal representations of the same assumption.  It introduces no new
physical or mathematical condition.
-/
theorem historyElement_countable
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    (H : OrderedPhysicalHistory D A O)
    (hCountable : HistoryAtMostCountable H) :
    Countable (HistoryElement H) := by

  rcases hCountable with ⟨encode, hInjective⟩

  exact hInjective.countable

/-
Linear order carried by one ordered physical history.

The physical precedence relation on the history has already been proved to
be a strict total order.  Mathlib can therefore package that relation as a
standard `LinearOrder`.

This introduces no additional ordering assumption.  In particular, the
strict order `<` of the resulting Lean structure is exactly the previously
defined `HistoryPrecedence H`.
-/
@[instance_reducible]
noncomputable def historyLinearOrder
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    (H : OrderedPhysicalHistory D A O) :
    LinearOrder (HistoryElement H) := by

  classical

  letI :
      IsStrictTotalOrder
        (HistoryElement H)
        (HistoryPrecedence H) :=
    historyPrecedence_isStrictTotalOrder H

  exact linearOrderOfSTO (HistoryPrecedence H)

/-
Existence of a real-valued order representation for an at-most-countable
ordered physical history.

The history has already been shown to carry a strict total order given
exactly by irreversible precedence.  If the history is finite or
countable, Mathlib's countable-order embedding theorem provides an order
embedding into the real numbers.

The result is stated directly in manuscript form rather than as Mathlib's
bundled `OrderEmbedding` type:

    t : H → ℝ.

The map is injective, and irreversible precedence is represented exactly
by the ordinary strict order on the real numbers:

    x ≺ y  ↔  t(x) < t(y).

Thus the scalar coordinate introduces no additional temporal ordering; it
is a numerical representation of the order already defined by physical
precedence.
-/
theorem history_orderEmbedsIntoReal
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    (H : OrderedPhysicalHistory D A O)
    (hCountable : HistoryAtMostCountable H) :
    ∃ t : HistoryElement H → Real,
      Function.Injective t ∧
      ∀ {x y : HistoryElement H},
        HistoryPrecedence H x y ↔ t x < t y := by

  let : LinearOrder (HistoryElement H) :=
    historyLinearOrder H

  let : Countable (HistoryElement H) :=
    historyElement_countable H hCountable

  obtain ⟨e⟩ :=
    Order.embedding_from_countable_to_dense
      (HistoryElement H)
      Real

  refine ⟨fun x => e x, e.injective, ?_⟩

  intro x y

  change (x < y) ↔ e x < e y

  exact e.lt_iff_lt.symm

/-
Strictly increasing reparametrizations preserve temporal order.

The real-valued coordinate obtained above is not unique.  Suppose

    t : H → ℝ

represents irreversible precedence on an ordered physical history, so that

    x ≺ y  ↔  t(x) < t(y).

Let

    f : ℝ → ℝ

be any strictly increasing function.  Then the composed coordinate

    f ∘ t

represents exactly the same precedence relation.

Thus the numerical values assigned by a temporal coordinate have no
independent physical significance at this stage.  What is fixed is only
their ordering.

Strict monotonicity also guarantees that f is injective, so composing with
f preserves the injectivity of the original temporal coordinate.
-/
theorem strictMono_reparametrization_preserves_temporalOrder
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    (H : OrderedPhysicalHistory D A O)
    (t : HistoryElement H → Real)
    (hInjective : Function.Injective t)
    (hOrder :
      ∀ {x y : HistoryElement H},
        HistoryPrecedence H x y ↔ t x < t y)
    {f : Real → Real}
    (hf : StrictMono f) :
    Function.Injective (fun x => f (t x)) ∧
    ∀ {x y : HistoryElement H},
      HistoryPrecedence H x y ↔
        f (t x) < f (t y) := by

  constructor

  · intro x y hxy
    apply hInjective
    apply hf.injective
    exact hxy

  · intro x y
    rw [hOrder]
    exact hf.lt_iff_lt.symm
    

/-
Bundle theorem — temporal-order characterization.

This theorem collects the principal conclusions of the temporal-order branch
in the same form in which they are used conceptually in the manuscript.

From operational reachability and the selected ordered physical history:

  1. irreversible precedence on reversible classes is a strict partial order;

  2. its restriction to an ordered physical history is a strict total order;

  3. when that history is finite or countable, the order admits an injective
     real-valued representation that preserves and reflects precedence.

No additional physical premise is introduced by this theorem.  It merely
packages conclusions already proved separately, so that the manuscript-level
dependency map can display the temporal-order result as one recognizable
endpoint.
-/
theorem temporalOrder_characterization
    {M : SBI}
    {C : NetworkRealizationContext M}
    {K : OperationalContext C}
    {D : ConfigurationChangeSemantics K}
    {A : OperationalAccessibilitySemantics D}
    {O : Observer M}
    (H : OrderedPhysicalHistory D A O)
    (hCountable : HistoryAtMostCountable H) :

    ((∀ q : ReversibleClass D A O,
        ¬ IrreversiblePrecedence D A O q q)
      ∧
      (∀ {q₁ q₂ q₃ : ReversibleClass D A O},
        IrreversiblePrecedence D A O q₁ q₂ →
        IrreversiblePrecedence D A O q₂ q₃ →
        IrreversiblePrecedence D A O q₁ q₃))
    ∧
    IsStrictTotalOrder
      (HistoryElement H)
      (HistoryPrecedence H)
    ∧
    (∃ t : HistoryElement H → Real,
      Function.Injective t ∧
      ∀ {x y : HistoryElement H},
        HistoryPrecedence H x y ↔ t x < t y) := by

  constructor

  · exact
      irreversiblePrecedence_strictPartialOrder
        D A O

  constructor

  · exact
      historyPrecedence_isStrictTotalOrder H

  · exact
      history_orderEmbedsIntoReal H hCountable

end SBI.Time
