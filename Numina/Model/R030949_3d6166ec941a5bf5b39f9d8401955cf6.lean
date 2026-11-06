import Mathlib

theorem algebra_336 (vArithmetic : ℝ) (h : 0 < vArithmetic)
  (h1 : 2 * 1185 /  (54 + vArithmetic) = 2.01 * 1185 / (54 + vArithmetic) + 2 * 1185 / (54 - vArithmetic))
  : round vArithmetic = 65 := by
  have h2 : 0.01 * 1185 / (54 + vArithmetic) + 2 * 1185 / (54 - vArithmetic) = 0 := by
    have h1' : 2 * 1185 / (54 + vArithmetic) = 2.01 * 1185 / (54 + vArithmetic) + 2 * 1185 / (54 - vArithmetic) := h1
    have eq1 : 2.01 * 1185 / (54 + vArithmetic) = 2 * 1185 / (54 + vArithmetic) + 0.01 * 1185 / (54 + vArithmetic) := by
      ring_nf
    rw [eq1] at h1
    linarith
  have h3 : (54 + vArithmetic) ≠ 0 := by
    by_contra h3
    have h4 : vArithmetic = -54 := by linarith
    rw [h4] at h
    norm_num at h
  have h4 : (54 - vArithmetic) ≠ 0 := by
    by_contra h4
    have h5 : vArithmetic = 54 := by linarith
    rw [h5] at h1
    norm_num [h5] at h1
  have h5 : 0.01 * 1185 * (54 - vArithmetic) + 2 * 1185 * (54 + vArithmetic) = 0 := by
    have h5 : 0.01 * 1185 / (54 + vArithmetic) + 2 * 1185 / (54 - vArithmetic) = 0 := h2
    field_simp [(show (54 + vArithmetic : ℝ) ≠ 0 by assumption), 
                (show (54 - vArithmetic : ℝ) ≠ 0 by assumption)] at h5 ⊢
    nlinarith
  have h6 : 0.01 * (54 - vArithmetic) = -2 * (54 + vArithmetic) := by
    nlinarith
  have h7 : 54 - vArithmetic = -200 * (54 + vArithmetic) := by
    nlinarith
  have h8 : vArithmetic < 0 := by
    nlinarith
  linarith