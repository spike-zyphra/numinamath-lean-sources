import Mathlib

/- Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that

$$
f\left(x^{2}+y\right) \geqslant\left(\frac{1}{x}+1\right) f(y)
$$

holds for all $x \in \mathbb{R} \backslash\{0\}$ and all $y \in \mathbb{R}$.

## Proposed by Uzbekistan -/
theorem algebra_606027 (f : ℝ → ℝ) : (∀ x ≠ 0, ∀ y : ℝ, f (x ^ 2 + y) ≥ (1 / x + 1) * f y) ↔
∀ y : ℝ, f y = 0 := by
  constructor
  -- Plug in $x=-1$ to heq, we can show that $f(y)$ is nonnegative for any $y$
  · intro heq; have fpos : ∀ y, 0 ≤ f y := by
      intro y; specialize heq (-1) (show _ by simp) (-1+y)
      simp at heq; exact heq
  -- Plug in $x=1/n$ for some nonzero natural number $n$ and use induction, we can prove the following auxillary lemma
    have aux : ∀ y, ∀ k n : ℕ, n ≠ 0 → (n + 1) ^ k * f y ≤ f (y + k / n ^ 2) := by
      intro y k n nne0; induction k with
      | zero => simp
      | succ k ihk =>
        rw [pow_succ', mul_assoc]; specialize heq ((1:ℝ)/n) (show _ by positivity) (y+k/n^2); calc
          _ ≤ ((n:ℝ) + 1) * f (y + k / n ^ 2) := by gcongr
          _ ≤ _ := by
            rw [ge_iff_le, one_div_div, div_one] at heq; apply le_trans heq
            push_cast; ring_nf; rfl
  -- To prove the main goal, we first plug in $k=n^2$ to aux
    intro y; have yaux : ∀ n : ℕ , n ≠ 0 → ((n : ℝ) + 1) ^ n ^ 2 * f y ≤ f (y + 1) := by
      intro n nne0; specialize aux y (n^2) n nne0; push_cast at aux
      rw [div_self] at aux; exact aux; positivity
  -- Specialize aux to $⌈f (y + 1) / f y⌉₊ + 1$ to get a contradiction from linear arithmetic
    by_contra! h; specialize yaux (Nat.ceil (f (y + 1) / f y) + 1) (show _ by simp)
    rw [← le_div_iff₀] at yaux; convert yaux; simp; calc
      _ ≤ (Nat.ceil (f (y + 1) / f y) : ℝ) := by apply Nat.le_ceil
      _ < Nat.ceil (f (y + 1) / f y) + 1 + 1 := by ring_nf; simp
      _ ≤ _ := by apply le_self_pow₀; simp; all_goals positivity
    apply lt_of_le_of_ne; apply fpos; exact Ne.symm h
-- Conversely, if $f(x)=0$ for all $x$, it is straightfoward to check the equation in question holds
  intro h; simp [h]