import Mathlib

theorem algebra_152897 (a : ℕ → ℝ) (h : ∀ n, ∑ i in Finset.Icc 1 n, a i = n ^ 3) :
    ∑ i in Finset.Icc 2 100, (1 / (a i - 1)) = 33 / 100 := by
  have ha1 : ∀ n : ℕ, a (n + 1) = 3 * ((n + 1 : ℕ) : ℝ) ^ 2 - 3 * ((n + 1 : ℕ) : ℝ) + 1 := by
    intro n
    have eq1 := h (n + 1)
    have eq2 := h n
    simp [Finset.sum_Icc_succ_top, mul_add, add_mul] at eq1 eq2 ⊢
    all_goals
      ring_nf at eq1 eq2 ⊢
      linarith
  have eq1 : ∀ i : ℕ, a (i + 1) - 1 = 3 * (i + 1 : ℝ) * (i : ℝ) := by
    intro i
    have ha1' := ha1 i
    simp [ha1']
    <;> ring
  -- Compute $\sum_{i=2}^{100} \frac{1}{a_i - 1}$ where $a_i - 1 = 3 \cdot i \cdot (i - 1)$ for $i \geq 2$
  norm_num [Finset.sum_Icc_succ_top, eq1]