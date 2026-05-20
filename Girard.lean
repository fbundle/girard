def isTrans (r: T → T → Prop): Prop :=
  ∀ a: T, ∀ b: T, ∀ c: T,
  (r a b) → (r b c) → (r a c)

def infChain {T} := Nat → T

def isWF (r: T → T → Prop): Prop :=
  ¬ (
    ∃ f: Nat → T,
    ∀ n: Nat,
    let x2 := f (n+1)
    let x1 := f n
    r x2 x1
  )

structure Poset T where
  rel: T → T → Prop
  trans: isTrans rel

structure WFPoset T extends Poset T where
  wf: isWF rel

-- coercion
instance: Coe (WFPoset T) (Poset T) where
  coe s := s.toPoset

structure P (u: Nat) where
  T: Type u
  carrier: WFPoset T

-- order preserving map
def preserveOrder (s1: Poset T) (s2: Poset V) (f: T → V): Prop :=
  ∀ a b: T,
  (s1.rel a b) → (s2.rel (f a) (f b))

-- prec - relation in P
def prec (s1: P u) (s2: P u): Prop :=
  ∃ (f: s1.T → s2.T),
  -- f preserves order
  preserveOrder (s1.carrier) (s2.carrier) f
  ∧
  -- exist dominate elem r
  ∃ r: s2.T,
  ∀ s: s2.T, ∃ t: s1.T, (f t = s) →
  s2.carrier.rel s r

def surjToP (f: α → P u): Prop :=
  ∀ s: P u,
  ∃ a: α,
  f a = s

theorem girard {T: Type u} : ¬ ∃ f: T → P u, surjToP f := by
  intro exist_surj_f
  rcases exist_surj_f with ⟨f, surj_f⟩
  dsimp [surjToP] at surj_f



  sorry
