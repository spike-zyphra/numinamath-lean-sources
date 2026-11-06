import Mathlib

theorem algebra_5326 (a : ℝ) (ha : a > 4) (c : ℤ) (h : ∃ x : ℝ, a * x ^ 2 + 18 * x + 6 * c = 0) :
    c ≤ 3 := by
  rcases h with ⟨x, hx⟩
  have h1 : (18 : ℝ) ^ 2 - 4 * a * (6 * (c : ℝ)) ≥ 0 := by
    nlinarith [sq_nonneg (a * x + 9), sq_nonneg (x + 2), sq_nonneg (a - 4), sq_nonneg ((x + 2) * (a - 4)), hx, sq_nonneg (x + 2), sq_nonneg (a * x), sq_nonneg ((a - 4) * x), sq_nonneg (a * (x + 2)), sq_nonneg ((x + 2) * (a - 4))]
  have h2 : (a : ℝ) * (c : ℝ) ≤ (13.5 : ℝ) := by
    nlinarith
  have h3 : (4 : ℝ) * (c : ℝ) < (13.5 : ℝ) := by
    nlinarith [show (a : ℝ) > (4 : ℝ) by linarith]
  have h4 : (c : ℝ) < (3.375 : ℝ) := by
    nlinarith
  have h5 : c ≤ 3 := by
    by_contra h6
    push_neg at h6
    have hc1 : c ≥ 4 := by
      omega
    have hc2 : (c : ℝ) ≥ (4 : ℝ) := by
      exact_mod_cast hc1
    nlinarith
  exact_mod_cast h5