/-
  Girard's Paradox
  ================
  Formalization of Martin-Löf's proof that a type theory with a "type of all
  types" (Type : Type) is inconsistent.  We work in universe `u` and show that
  the collection 𝒫 of all well-founded posets in `u` cannot itself be a type
  in `u`; if it were, we could derive `False`.

  We follow the argument in the accompanying .tex note almost step by step.
  The sections below correspond to the sections of that note.
-/

universe u


-- ============================================================
-- §1  Posets and well-foundedness
-- ============================================================

/-
  The .tex defines a *poset* as a set with a transitive relation `<`, and calls
  it *well-founded* (wf X) when it has no infinite descending chain.

  We encode this as a structure `WFPoset T` over a carrier type `T`.
  Using `Type u` as the ambient universe means every WFPoset lives at level u.
-/

/-- A relation is transitive when x < y and y < z imply x < z. -/
def isTrans {T : Type u} (rel : T → T → Prop) : Prop :=
  ∀ {a b c : T}, rel a b → rel b c → rel a c

/-- A relation is well-founded when there is no infinite descending chain
    … < xₙ < xₙ₋₁ < … < x₁ < x₀. -/
def isWF {T : Type u} (rel : T → T → Prop) : Prop :=
  ¬ ∃ f : Nat → T, ∀ n : Nat, rel (f (n + 1)) (f n)

/-- A well-founded poset bundles a carrier type with its transitive,
    well-founded strict order. -/
structure WFPoset (T : Type u) where
  rel   : T → T → Prop
  trans : isTrans rel
  wf    : isWF rel


-- ============================================================
-- §2  The collection 𝒫 of all well-founded posets
-- ============================================================

/-
  The .tex lets 𝒫 = { S : Set | wf S }.  In type theory we package this as
  the structure `PType`, which pairs a carrier type T : Type u with a
  WFPoset structure on T.

  The whole point of the paradox is to show that `PType.{u}` cannot itself
  live in `Type u`; the theorem `girard` below makes this precise.
-/

/-- `PType` is the collection of all well-founded posets at universe level u. -/
structure PType where
  T       : Type u
  carrier : WFPoset T


-- ============================================================
-- §3  The ordering ≺ on 𝒫
-- ============================================================

/-
  Given S, R ∈ 𝒫, the .tex defines  S ≺ R  when there exists an
  order-preserving map  φ : S → R  whose image is bounded above in R,
  i.e. ∃ r ∈ R, ∀ x ∈ im φ, x < r.
-/

/-- `pLt S R` (written S ≺ R) holds when there is an order-preserving
    map φ : S.T → R.T whose image has an upper bound in R.T. -/
def pLt (S R : PType.{u}) : Prop :=
  ∃ (φ : S.T → R.T),
    (∀ (x y : S.T), S.carrier.rel x y → R.carrier.rel (φ x) (φ y)) ∧
    (∃ (r : R.T), ∀ (x : S.T), R.carrier.rel (φ x) r)

/-- ≺ is transitive: given φ : A → B and ψ : B → C, compose them.
    The bound for ψ ∘ φ in C is the bound of ψ in C. -/
theorem pLt_isTrans : isTrans pLt := by
  intro _ _ _ ⟨f, hf_ord, _, hf_bnd⟩ ⟨g, hg_ord, rc, hg_bnd⟩
  exact ⟨g ∘ f, fun x y h => hg_ord _ _ (hf_ord _ _ h), rc, fun x => hg_bnd (f x)⟩


-- ============================================================
-- §4  𝒫 with ≺ is itself well-founded
-- ============================================================

/-
  The .tex argues: assume for contradiction there is an infinite chain
      … ≺ Sₙ ≺ Sₙ₋₁ ≺ … ≺ S₁ ≺ S₀  in 𝒫.
  For each n let  φₙ : Sₙ₊₁ → Sₙ  and  rₙ ∈ Sₙ  witness Sₙ₊₁ ≺ Sₙ.
  Compose:  ψₙ = φ₀ ∘ φ₁ ∘ … ∘ φₙ₋₁ : Sₙ → S₀.
  Then  ψₙ(rₙ)  is a descending chain in S₀, contradicting wf S₀.
-/

theorem pLt_isWF : isWF pLt := by
  intro ⟨chain, hchain⟩
  -- hchain n : chain(n+1) ≺ chain(n), i.e. ∃ φₙ, order-preserving with bound rₙ
  -- Extract φₙ and rₙ via classical choice (we need actual functions)
  let φ : ∀ n, (chain (n + 1)).T → (chain n).T :=
    fun n => (hchain n).choose
  have hφ_spec : ∀ n,
      (∀ x y, (chain (n + 1)).carrier.rel x y → (chain n).carrier.rel (φ n x) (φ n y)) ∧
      ∃ (rn : (chain n).T), ∀ x, (chain n).carrier.rel (φ n x) rn :=
    fun n => (hchain n).choose_spec
  have hφ_ord : ∀ n x y, (chain (n + 1)).carrier.rel x y →
      (chain n).carrier.rel (φ n x) (φ n y) := fun n => (hφ_spec n).1
  -- rₙ ∈ chain(n) is the bound: ∀ x, φₙ(x) < rₙ
  let r : ∀ n, (chain n).T :=
    fun n => ((hφ_spec n).2).choose
  have hr : ∀ n x, (chain n).carrier.rel (φ n x) (r n) :=
    fun n => ((hφ_spec n).2).choose_spec
  -- ψₙ : chain(n).T → chain(0).T is φ₀ ∘ … ∘ φₙ₋₁, built by recursion
  let ψ : ∀ (n : Nat), (chain n).T → (chain 0).T :=
    fun n => Nat.rec (motive := fun n => (chain n).T → (chain 0).T)
              id (fun k ψk => ψk ∘ φ k) n
  -- ψₙ is order-preserving (by induction: ψ₀ = id, ψₙ₊₁ = ψₙ ∘ φₙ)
  have hψ_ord : ∀ n x y, (chain n).carrier.rel x y →
      (chain 0).carrier.rel (ψ n x) (ψ n y) := by
    intro n
    induction n with
    | zero      => intro x y h; exact h
    | succ n ih => intro x y h; exact ih _ _ (hφ_ord n x y h)
  -- The sequence  n ↦ ψₙ(rₙ)  descends in chain(0):
  --   ψₙ₊₁(rₙ₊₁) = ψₙ(φₙ(rₙ₊₁)) < ψₙ(rₙ)  because φₙ(rₙ₊₁) < rₙ
  exact (chain 0).carrier.wf
    ⟨fun n => ψ n (r n), fun n => hψ_ord n _ _ (hr n (r (n + 1)))⟩


-- ============================================================
-- §5  Initial segments
-- ============================================================

/-
  The .tex defines the *initial segment* of S at r as
      Sᵣ = { y ∈ S | y < r },
  with the induced order.  If S is well-founded, so is Sᵣ.

  In Lean we use the Subtype  {y : S.T // S.carrier.rel y r}  (note `//`,
  not `|`; the latter would give a `Set`, not a `Type`).
-/

/-- The initial segment of S at r is the sub-poset of all elements strictly
    below r.  It is again a well-founded poset. -/
def initSeg (S : PType.{u}) (r : S.T) : PType.{u} where
  T       := {y : S.T // S.carrier.rel y r}
  -- Inherit the relation and its properties from S
  carrier := ⟨fun x y => S.carrier.rel x.1 y.1,
              fun h1 h2 => S.carrier.trans h1 h2,
              fun ⟨c, hc⟩ => S.carrier.wf ⟨fun n => (c n).1, hc⟩⟩

/-
  The .tex uses initial segments to exhibit the ordering ≺ in two ways:

  (a) If x < y in S then Sₓ ≺ Sᵧ.
      Witness: the inclusion ι : Sₓ → Sᵧ,  ι⟨z, z<x⟩ = ⟨z, z<y⟩  (by trans).
      Bound in Sᵧ: the element ⟨x, x<y⟩.

  (b) Sᵣ ≺ S for any r ∈ S.
      Witness: the inclusion ι : Sᵣ → S,  ι⟨s, s<r⟩ = s.
      Bound in S: r itself.
-/

/-- x < y in S implies Sₓ ≺ Sᵧ (the inclusion with bound ⟨x, h⟩). -/
theorem initSeg_lt {S : PType.{u}} {x y : S.T} (h : S.carrier.rel x y) :
    pLt (initSeg S x) (initSeg S y) := by
  refine ⟨fun ⟨z, hz⟩ => ⟨z, S.carrier.trans hz h⟩, fun _ _ hrel => hrel, ⟨x, h⟩, ?_⟩
  intro ⟨_, hz⟩; exact hz

/-- The initial segment Sₜ is strictly below S in ≺ (the inclusion with bound t). -/
theorem initSeg_lt_self (S : PType.{u}) (t : S.T) : pLt (initSeg S t) S := by
  refine ⟨fun ⟨s, _⟩ => s, fun _ _ h => h, t, ?_⟩
  intro ⟨_, hs⟩; exact hs


-- ============================================================
-- §6  Girard's Paradox
-- ============================================================

/-
  The .tex concludes as follows.

  Since (𝒫, ≺) is well-founded, 𝒫 is itself a well-founded poset, so 𝒫 ∈ 𝒫.
  Write P for 𝒫 viewed as an element of itself.

  For every S ∈ 𝒫, define  gₛ : S → P  by  r ↦ Sᵣ  (the initial segment).
  This makes S ≺ P.  In particular, P ≺ P.

  But P ≺ P means P has a strictly self-referential element, which (by
  Lemma 3 in the .tex, or equivalently by `pLt_isWF`) is impossible.

  ──────────────────────────────────────────────────────────────────────────
  In type theory, "𝒫 is a set" would mean PType.{u} : Type u, i.e. there
  is a surjection f : T →  PType.{u} for some T : Type u.  The theorem
  below shows no such surjection can exist, hence PType.{u} ∉ Type u.
  ──────────────────────────────────────────────────────────────────────────

  Concretely:

  Step 1.  Use f to pull ≺ back to T:  x ≺ᵀ y  iff  f(x) ≺ f(y).
           The pullback (T, ≺ᵀ) is a WFPoset.  Call the resulting element P ∈ 𝒫.

  Step 2.  Fix a section  sec : 𝒫 → T  of f  (so f(sec(s)) = s).
           Define  g : P.T → P.T  by  g(t) = sec(Pₜ)
           (the initial segment of P at t, pulled back to T via sec).
           Then f(g(t)) = Pₜ.

  Step 3.  g is order-preserving (because t < t' in P implies Pₜ ≺ Pₜ′),
           and g is bounded above by sec(P)  (because Pₜ ≺ P for all t).
           Hence P ≺ P.

  Step 4.  P ≺ P gives the constant chain P, P, P, … in 𝒫, contradicting
           `pLt_isWF`.
-/

theorem girard {T : Type u} (f : T → PType.{u})
    (h_surj : ∀ s : PType.{u}, ∃ t : T, f t = s) : False := by

  -- Step 1: fix a section sec with f(sec s) = s
  let sec : PType.{u} → T := fun s => (h_surj s).choose
  have hsec : ∀ s : PType.{u}, f (sec s) = s := fun s => (h_surj s).choose_spec

  -- Step 1 (cont.): pull ≺ back through f to make T a WFPoset
  let relT : T → T → Prop := fun x y => pLt (f x) (f y)
  have relT_trans : isTrans relT := fun h1 h2 => pLt_isTrans h1 h2
  -- A descending chain in (T, relT) maps to one in (𝒫, ≺), contradicting pLt_isWF
  have relT_wf : isWF relT := fun ⟨c, hc⟩ => pLt_isWF ⟨f ∘ c, hc⟩
  -- P ∈ 𝒫 is the well-founded poset (T, relT)
  let P : PType.{u} := ⟨T, ⟨relT, relT_trans, relT_wf⟩⟩

  -- Step 2: define g(t) = sec(Pₜ), so f(g(t)) = Pₜ
  let g : T → T := fun t => sec (initSeg P t)
  have hfg : ∀ t, f (g t) = initSeg P t := fun t => hsec (initSeg P t)

  -- Step 3a: g is order-preserving
  --   t <ᵀ t'  means  f(t) ≺ f(t'),  i.e. Pₜ ≺ Pₜ′  (by initSeg_lt)
  have hg_ord : ∀ x y : T, relT x y → relT (g x) (g y) := by
    intro x y hxy
    show pLt (f (g x)) (f (g y))
    rw [hfg, hfg]
    exact initSeg_lt hxy

  -- Step 3b: g is bounded above by sec(P)
  --   f(g(t)) = Pₜ ≺ P = f(sec P)  by initSeg_lt_self
  have hg_bnd : ∀ x : T, relT (g x) (sec P) := by
    intro x
    show pLt (f (g x)) (f (sec P))
    rw [hfg, hsec]
    exact initSeg_lt_self P x

  -- Step 3c: g witnesses P ≺ P
  have hPP : pLt P P := ⟨g, hg_ord, sec P, hg_bnd⟩

  -- Step 4: the constant chain P, P, P, … contradicts pLt_isWF
  exact pLt_isWF ⟨fun _ => P, fun _ => hPP⟩
