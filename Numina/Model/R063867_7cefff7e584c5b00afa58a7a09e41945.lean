import Mathlib

theorem algebra_128336 (v : ℝ) (h : v > 0) (h1 : 6 / (v + 5) + 6 / (v - 5) = 30 / 60) :
    v = 25 := by
  have h2 : v + 5 ≠ 0 := by
    linarith
  have h3 : v - 5 ≠ 0 := by
    by_contra h4
    have h4' : v = 5 := by linarith
    rw [h4'] at h1
    norm_num at h1
    <;> linarith
  field_simp [(show v + 5 ≠ 0 by linarith), (show v - 5 ≠ 0 by assumption)] at h1
  ring_nf at h1
  have h4 : v^2 - 24 * v - 25 = 0 := by
    nlinarith [sq_pos_of_pos h]
  have h5 : (v - 25) * (v + 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Case v = 25
    linarith
  · -- Case v = -1 which contradicts h: v > 0
    nlinarith