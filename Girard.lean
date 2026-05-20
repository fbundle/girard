universe u

-- Standard definitions for Girard's Paradox

/-- Transitivity of a relation. -/
def isTrans {T : Type u} (rel : T → T → Prop) : Prop :=
  ∀ {a b c : T}, rel a b → rel b c → rel a c

/-- Well-foundedness of a relation (no infinite descending chains). -/
def isWF {T : Type u} (rel : T → T → Prop) : Prop :=
  ¬ ∃ f : Nat → T, ∀ n : Nat, rel (f (n + 1)) (f n)

/-- A well-founded poset is a type with a transitive, well-founded relation. -/
structure WFPoset (T : Type u) where
  rel : T → T → Prop
  trans : isTrans rel
  wf : isWF rel

/-- PType is the "collection" of all well-founded posets in universe u. -/
structure PType where
  T : Type u
  carrier : WFPoset T


/-- PType u is too large to be indexed by any type in universe u. -/
theorem girard {T : Type u} (f : T → PType.{u}) (h_surj : ∀ s : PType.{u}, ∃ t : T, f t = s) : False := by
  sorry
