import Mathlib

theorem algebra_6807 (a : ℝ) (ha : a > 3) (c : ℤ) (h : ∃ x : ℝ, a * x ^ 2 + 7 * x - c = 0) :
    c ≥ -4 := by
  rcases h with ⟨x, hx⟩
  have h1 : (2 * a * x + 7) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h2 : 4 * a * (c : ℝ) + 49 ≥ 0 := by
    have eq1 : a * x ^ 2 + 7 * x - (c : ℝ) = 0 := by
      simpa using hx
    have eq2 : (c : ℝ) = a * x ^ 2 + 7 * x := by
      nlinarith
    have eq3 : 4 * a * (c : ℝ) + 49 = (2 * a * x + 7) ^ 2 := by
      rw [eq2]
      ring
    nlinarith [eq3, h1]
  by_contra h3
  push_neg at h3
  have h4 : c ≤ -5 := by omega
  have h5 : (c : ℝ) ≤ (-5 : ℝ) := by
    exact_mod_cast h4
  nlinarith [h2, h5, mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < (4 : ℝ) by norm_num)]