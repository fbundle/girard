
def isTrans (rel: T → T → Prop): Prop :=
  ∀ {a b c: T}, (rel a b) → (rel b c) → (rel a c)

structure Poset T where
  rel: T → T → Prop
  trans: isTrans rel

def isWF (rel: T → T → Prop): Prop :=
  ¬ (
    ∃ f: Nat → T,
    ∀ n: Nat,
    let x2 := f n.succ
    let x1 := f n
    rel x2 x1
  )

structure WFPoset T extends Poset T where
  wf: isWF rel

-- coercion
instance: Coe (WFPoset T) (Poset T) where
  coe s := s.toPoset

structure PType (u: Nat) where
  T: Type u
  carrier: WFPoset T

-- order preserving map
def preserveOrder (s1: Poset T) (s2: Poset V) (f: T → V): Prop :=
  ∀ a b: T,
  (s1.rel a b) → (s2.rel (f a) (f b))

-- prec - relation in P
def prec (s1: PType u) (s2: PType u): Prop :=
  ∃ (f: s1.T → s2.T),
  -- f preserves order
  preserveOrder (s1.carrier) (s2.carrier) f
  ∧
  -- exist dominate elem r
  ∃ r: s2.T,
  ∀ s: s2.T, ∃ t: s1.T, (f t = s) →
  s2.carrier.rel s r

-- exercise for readers
def PisTrans: @isTrans (PType u) prec :=
  sorry

-- construct well-founded poset P
def P: Poset (PType u) := {
  rel := prec,
  trans := PisTrans,
}

noncomputable def aoc {α : Type u} {P : α → Prop} (h : ∃ x, P x) : { x // P x } :=
  ⟨Classical.choose h, Classical.choose_spec h⟩


def PisWF: @isWF (PType u) P.rel := by
  dsimp [isWF]
  intro existsSeq
  rcases existsSeq with ⟨S, hS⟩

  let s (n: Nat): (S n).T :=
    let Sn1_lt_Sn := hS n
    let ⟨fn , ⟨_, RDominates⟩⟩  := aoc Sn1_lt_Sn
    let ⟨r, hr⟩ := aoc RDominates
    r

  let f (n: Nat): (S (n+1)).T → (S n).T :=
    let Sn1_lt_Sn := hS n
    let ⟨fn , ⟨_, RDominates⟩⟩  := aoc Sn1_lt_Sn
    fn

  let rec lift {k: Nat} {n: Nat} (s': (S (n + k)).T): (S n).T :=
    match k with
      | 0 => s' -- S_n → S_n
      | Nat.succ k1 =>
        let h_eq : (n + Nat.succ k1) = (Nat.succ n + k1) := by
          rw [Nat.add_succ, Nat.succ_add]
        let s_casted := cast (by rw [h_eq]) s'
        (f n) (lift s_casted)

  let liftToS0 (n: Nat) (s': (S n).T): (S 0).T :=
    let h_eq: (0 + n) = n := by simp
    let s_casted := cast (by rw [h_eq]) s'
    lift s_casted

  let f (n: Nat): (S 0).T :=
    let h_eq: (0 + n) = n := by simp
    let s_casted := cast (by rw [h_eq]) (s n)
    lift s_casted

  have S0WF := (S 0).carrier.wf
  dsimp [isWF] at S0WF


  have hf: ∀ (n: Nat), (S 0).carrier.rel (f n.succ) (f n) := by
    intro n


    sorry


  exact S0WF ⟨f, hf⟩





def surjToP (f: T → PType u): Prop :=
  ∀ s: PType u,
  ∃ x: T,
  f x = s

theorem girard {T: Type u}: ¬ ∃ (f: T → PType u), surjToP f :=
  sorry
