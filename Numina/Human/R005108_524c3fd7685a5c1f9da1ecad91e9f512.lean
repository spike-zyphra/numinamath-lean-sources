import Mathlib

-- $$
-- c_{i}= \begin{cases}a_{i} & \text { als } a_{i}=a_{i-1} \\ b_{i} & \text { als } b_{i}=b_{i-1}\end{cases}
-- $$
inductive Step (a₀ b₀ c_sum₀: ℕ) : (n a b c : ℕ) → Prop where
  | C0 : Step _ _ _ 0 a₀ b₀ c_sum₀
  | CA : Step _ _ _ n a b c_sum → Step _ _ _ (n + 1) (a + 1) b (c_sum + b)
  -- ^ Go for `a`, `b` unchanged, so we accumulate `c` by `b`.
  | CB : Step _ _ _ n a b c_sum → Step _ _ _ (n + 1) a (b + 1) (c_sum + a)
open Step

lemma step_pos_a (a b k c : ℕ) : Step 1 1 0 k a b c → a > 0 := by
  intro h
  induction h with
  | C0 => simp
  | CA => omega
  | CB => omega

lemma step_pos_b (a b k c : ℕ) : Step 1 1 0 k a b c → b > 0 := by
  intro h
  induction h with
  | C0 => simp
  | CA => omega
  | CB => omega

/-
We prove by induction on $j$ that $c_{1}+\ldots+c_{j}=a_{j} b_{j}-1$. For $j=1$, this reads $c_{1}=a_{1} b_{1}-1$ and this is true since $\left(a_{1}, b_{1}\right) \in\{(1,2),(2,1)\}$. Now assume that $c_{1}+\ldots+c_{i-1}=a_{i-1} b_{i-1}-1$. Without loss of generality, assume that $\left(a_{i}, b_{i}\right)=$ $\left(a_{i-1}, 1+b_{i-1}\right)$, so that $a_{i}=a_{i-1}$ and thus $c_{i}=a_{i-1}$. We now have

$$ \left(c_{1}+\ldots+c_{i-1}\right)+c_{i}=\left(a_{i-1} b_{i-1}-1\right)+a_{i-1}=a_{i-1}\left(b_{i-1}+1\right)-1=a_{i} b_{i}-1 $$

which completes the induction. For $j=k$ we now see that $c_{1}+\ldots+c_{k}=a_{k} b_{k}-1=n^{2}-1$.
-/
lemma lemma1 (a b k c : ℕ) : Step 1 1 0 k a b c → c = (a*b - 1) :=
by
  intro h
  induction h with
  | C0 => simp
  | @CA n a' b' c' s ih =>
      have : a' ≥ 1 := by apply step_pos_a; assumption
      have : b' ≥ 1 := by apply step_pos_b; assumption
      ring_nf
      rw [ih]
      zify
      repeat rw [Nat.cast_sub]
      push_cast
      ring_nf
      omega
      apply Right.one_le_mul
      <;> assumption
  | @CB n a' b' c' s ih =>
      have : a' ≥ 1 := by apply step_pos_a; assumption
      have : b' ≥ 1 := by apply step_pos_b; assumption
      ring_nf
      rw [ih]
      zify
      repeat rw [Nat.cast_sub]
      push_cast
      ring_nf
      omega
      apply Right.one_le_mul
      <;> assumption

/-
Zij $n$ een positief geheel getal. We bekijken rijtjes getallen $a_{0}, a_{1}, \ldots, a_{k}$ en $b_{0}, b_{1}, \ldots, b_{k}$ die voldoen aan $a_{0}=b_{0}=1$ en $a_{k}=b_{k}=n$ en waarbij voor elke $i$ met $1 \leq i \leq k$ geldt dat $\left(a_{i}, b_{i}\right)$ gelijk is aan ofwel $\left(1+a_{i-1}, b_{i-1}\right)$ ofwel $\left(a_{i-1}, 1+b_{i-1}\right)$. Definieer voor $1 \leq i \leq k$ het getal

$$
c_{i}= \begin{cases}a_{i} & \text { als } a_{i}=a_{i-1} \\ b_{i} & \text { als } b_{i}=b_{i-1}\end{cases}
$$

Bewijs dat $c_{1}+c_{2}+\cdots+c_{k}=n^{2}-1$.
-/
theorem combinatorics_605577 (n k c_sum: ℕ) : Step 1 1 0 k n n c_sum → c_sum = (n^2 - 1) :=
by
  intro h
  have := lemma1 _ _ _ _ h
  ring_nf at *
  assumption
