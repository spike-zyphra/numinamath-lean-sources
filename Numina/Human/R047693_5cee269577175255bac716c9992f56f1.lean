import Mathlib

open Real

/- 1. Given non-negative real numbers $x_{1}, x_{2}, \cdots, x_{n}$, if $x_{1}+x_{2}+\cdots+x_{n}=n$, prove:

$$

\frac{x_{1}}{1+x_{1}^{2}}+\frac{x_{2}}{1+x_{2}^{2}}+\cdots+\frac{x_{n}}{1+x_{n}^{2}} \leqslant \frac{1}{1+x_{1}}+\frac{1}{1+x_{2}}+\cdots+\frac{1}{1+x_{n}} \text {. }

$$

(1989 Soviet Ministry of Education Recommended Problem) -/
theorem inequalities_183506 (n : ℕ) (x : Fin n → ℝ)
    (h₀ : ∀ i, 0 ≤ x i) (h₁ : ∑ i, x i = n) :
    ∑ i, x i / (1 + x i ^ 2) ≤ ∑ i, 1 / (1 + x i) := by
    suffices ∑ i, (x i / (1 + x i ^ 2) - 1 / (1 + x i)) ≤ 0 by
      simp_all only [tsub_le_iff_right, Finset.sum_sub_distrib, zero_add]
    have : ∑ k, (x k / (1 + x k ^ 2) - 1 / (1 + x k)) ≤ ∑ k, (x k - 1) / 4 := by
      apply Finset.sum_le_sum
      intro k _
      have h1 : 0 < (1 + x k) := by
          have := h₀ k
          linarith
      have h2 : 0 < (1 + x k ^ 2) := by
        suffices 0 ≤ x k ^ 2 by linarith
        simp_all only [pow_nonneg]
      have h3 : 0 < (1 + x k ^ 2) * (1 + x k) := by
        simp_all only [mul_pos_iff_of_pos_left]
      -- For 1⩽k⩽n, we have x_k / (1 - x_k²) - 1 / (1 + x_k) = (x_k - 1) / ((1 + x_k²) (1 + x_k)).
      have : x k / (1 + x k ^ 2) - 1 / (1 + x k) = (x k - 1) / ((1 + x k ^ 2) * (1 + x k)) := by
        rw [div_sub_div _ _ (by linarith) (by linarith)]
        ring
      -- If x_k ≤ 1, then (1 + x_k²)(1 + x_k) ≥ 4, if x_k < 1 then (1 + x_k²)(1+x_k) < 4. Therefore, in any case, we have (x_k - 1)/((1 + x_k^2)(1 + x_k)) ≤ (x_k - 1)/4.
      have : (x k - 1) / ((1 + x k ^ 2) * (1 + x k)) ≤ (x k - 1) / 4 := by
        rcases lt_trichotomy (x k) 1 with h' | h' | h'
        · suffices (1 - x k) / 4 ≤ (1 - x k) / ((1 + x k ^ 2) * (1 + x k)) by
            apply le_of_neg_le_neg
            rw [← neg_div, neg_sub, ← neg_div, neg_sub]
            assumption
          apply (div_le_div_iff_of_pos_left (by simp_all) (by simp) h3).2
          suffices ((1 + x k ^ 2) * (1 + x k)) < 2 * 2 by linarith
          have h1' : 1 + x k ≤ 2 := by linarith
          have h2' : 1 + x k ^ 2 < 2 := by
            suffices x k ^ 2 < 1 by linarith
            exact (sq_lt_one_iff₀ (h₀ k)).mpr h'
          apply mul_lt_mul_of_pos_of_nonneg' h2' h1' h1 (by simp)
        · simp_all
        · apply (div_le_div_iff_of_pos_left (by simp_all) h3 (by simp)).2
          have h1' : 2 ≤ 1 + x k := by linarith
          have h2' : 2 < 1 + x k ^ 2 := by
            suffices 1 < x k ^ 2 by linarith
            exact (one_lt_sq_iff₀ (by linarith)).2 h'
          suffices 2 * 2 < (1 + x k ^ 2) * (1 + x k) by linarith
          apply mul_lt_mul_of_pos_of_nonneg' h2' h1' (by simp) (by linarith)
      simp_all only [mul_pos_iff_of_pos_left]
    suffices ∑ i, ((x i - 1) / 4) = 0 by linarith
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp [h₁]