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


def P (T: Type u) := WFPoset T

def surjectiveToP (f: α → P T): Prop :=
  ∀ (s: P T),
  ∃ (a: α),
  s = f a

theorem girard: ¬ (∃ f: α → P T, surjectiveToP f) := by
  intro exists_f
  rcases exists_f with ⟨f, f_surj⟩

  sorry
