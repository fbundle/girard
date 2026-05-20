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

structure P (u: Nat) where
  carrier {T: Type u}: WFPoset T


def surjToP (f: α → P u): Prop :=
  ∀ s: P u,
  ∃ a: α,
  f a = s

theorem girard {T: Type u} : ¬ ∃ f: T → P u, surjToP f :=
  sorry
