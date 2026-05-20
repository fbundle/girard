# Girard's Paradox

Supplement to [girard.pdf](https://fbundle.github.io/assets/public_doc/1_original_notes/girard/main.pdf)

A Lean 4 formalization of Martin-Löf's proof that a type theory admitting `Type : Type` is inconsistent. The argument is due to Girard (1972), refined by Martin-Löf (1972).

The full mathematical argument is in [`Girard.tex`](Girard.tex). The Lean proof is in [`Girard.lean`](Girard.lean). The sections below follow both files in parallel.

---

## §1 Posets and well-foundedness

A **poset** `X` is a set with a transitive relation `<`:

$$x < y \text{ and } y < z \implies x < z$$

A poset is **well-founded** (`wf X`) if it has no infinite descending chain:

$$\cdots < x_n < x_{n-1} < \cdots < x_1 < x_0$$

In Lean, these are `isTrans` and `isWF`, and the combined structure is `WFPoset T`.

> **Lemma.** If `x < x` for some `x ∈ X`, then `X` is not well-founded, since `x < x` produces the constant descending chain `… < x < x`.

---

## §2 The collection 𝒫 of all well-founded posets

$$\mathcal{P} = \{ S : \mathbf{Set} \mid \mathrm{wf}\, S \}$$

In Lean, this is `PType`: a structure pairing a carrier type `T : Type u` with a `WFPoset T`. The whole paradox turns on whether `PType.{u}` can itself live in `Type u`.

---

## §3 The ordering ≺ on 𝒫

For $S, R \in \mathcal{P}$, define $S \prec R$ when there exists an order-preserving map $\varphi : S \to R$ whose image is bounded above in $R$:

$$\exists\, r \in R,\; \forall\, x \in \mathrm{im}\,\varphi,\; x < r$$

In Lean this is `pLt`. The relation is transitive (`pLt_isTrans`): given $\varphi : A \to B$ and $\psi : B \to C$, the composition $\psi \circ \varphi$ is order-preserving and the bound of $\psi$ in $C$ serves as the bound for the composition.

---

## §4 𝒫 with ≺ is itself well-founded

**Claim.** $(\mathcal{P}, \prec)$ is well-founded.

**Proof** (`pLt_isWF`). Suppose for contradiction there is an infinite descending chain in $\mathcal{P}$:

$$\cdots \prec S_n \prec S_{n-1} \prec \cdots \prec S_1 \prec S_0$$

Let $\varphi_n : S_{n+1} \to S_n$ and $r_n \in S_n$ witness each step ($\varphi_n$ is order-preserving, $r_n$ bounds its image). Define the composition

$$\psi_n = \varphi_0 \circ \varphi_1 \circ \cdots \circ \varphi_{n-1} : S_n \to S_0$$

Then $\psi_n(r_n)$ is a strictly descending chain in $S_0$:

$$\cdots < \psi_n(r_n) < \psi_{n-1}(r_{n-1}) < \cdots < \psi_0(r_0)$$

because $\varphi_n(r_{n+1}) < r_n$, so $\psi_{n+1}(r_{n+1}) = \psi_n(\varphi_n(r_{n+1})) < \psi_n(r_n)$. This contradicts $\mathrm{wf}\, S_0$. $\square$

**Consequence.** Since $(\mathcal{P}, \prec)$ is a well-founded poset, $\mathcal{P} \in \mathcal{P}$. Write $P$ for $\mathcal{P}$ viewed as an element of itself.

---

## §5 Initial segments

For a poset $S$ and element $r \in S$, the **initial segment** at $r$ is:

$$S_r = \{ y \in S \mid y < r \}$$

with the order inherited from $S$. If $S$ is well-founded, so is $S_r$.

In Lean, `initSeg S r` uses the Subtype `{y : S.T // S.carrier.rel y r}` (with `//`, not `|` — the latter gives `Set S.T = S.T → Prop`, not a `Type`).

Two key lemmas:

- **`initSeg_lt`**: if $x < y$ in $S$, then $S_x \prec S_y$. The inclusion $\iota : S_x \hookrightarrow S_y$, sending $z \mapsto z$, is order-preserving, and $x$ (viewed as an element of $S_y$) bounds the image.

- **`initSeg_lt_self`**: $S_r \prec S$ for any $r \in S$. The inclusion $S_r \hookrightarrow S$ is order-preserving, with bound $r$.

For every $S \in \mathcal{P}$, define $g_S : S \to P$ by $r \mapsto S_r$. This makes $S \prec P$. In particular, taking $S = P$, we get $P \prec P$.

---

## §6 Girard's Paradox

In type theory, "$\mathcal{P}$ is a set" means `PType.{u} : Type u`, which is equivalent to the existence of a surjection $f : T \twoheadrightarrow \mathcal{P}$ for some $T : \mathtt{Type}\,u$. The main theorem shows no such surjection exists.

**Theorem** (`girard`). There is no surjection $f : T \to \mathcal{P}$ with $T : \mathtt{Type}\,u$.

**Proof.**

1. **Pull back ≺ to $T$.** Define $x \prec^T y \iff f(x) \prec f(y)$. Then $(T, \prec^T)$ is a well-founded poset — call it $P \in \mathcal{P}$.

2. **Fix a section.** Since $f$ is surjective, choose $\mathrm{sec} : \mathcal{P} \to T$ with $f(\mathrm{sec}(s)) = s$.

3. **Construct $g : P \to P$.** Set $g(t) = \mathrm{sec}(P_t)$, the initial segment of $P$ at $t$ pulled back to $T$ via $\mathrm{sec}$. Then $f(g(t)) = P_t$.
   - **Order-preserving**: $t \prec^T t'$ means $f(t) \prec f(t')$, i.e. $P_t \prec P_{t'}$ (by `initSeg_lt`), i.e. $g(t) \prec^T g(t')$.
   - **Bounded**: $f(g(t)) = P_t \prec P = f(\mathrm{sec}(P))$ (by `initSeg_lt_self`), so $g(t) \prec^T \mathrm{sec}(P)$.

4. **Conclude $P \prec P$.** The map $g$ with bound $\mathrm{sec}(P)$ witnesses $P \prec P$.

5. **Contradiction.** The constant sequence $P, P, P, \ldots$ is an infinite descending chain in $(\mathcal{P}, \prec)$, contradicting `pLt_isWF`. $\square$

---

## Building

```sh
lake build
```

Requires Lean 4 (tested on v4.29.1). No Mathlib dependency.
