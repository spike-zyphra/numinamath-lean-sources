import Mathlib

theorem algebra_101308 {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hdist : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (h1 : (a^2012 - c^2012) * (a^2012 - d^2012) = 2011) (h2 : (b^2012 - c^2012) * (b^2012 - d^2012) = 2011) :
    (c * d)^2012 - (a * b)^2012 = 2011 := by
  have a2012_ne_b2012 : a^2012 ≠ b^2012 := by
    by_contra h
    have : a = b := by
      have h1 : a^2012 = b^2012 := h
      have h2 : a > 0 := ha
      have h3 : b > 0 := hb
      rw [pow_left_inj (by linarith) (by linarith) (by norm_num)] at h1
      linarith
    tauto

  have h3 : (a^2012 - b^2012) * (a^2012 + b^2012 - (c^2012 + d^2012)) = 0 := by
    nlinarith [h1, h2, pow_pos ha 2012, pow_pos hb 2012, pow_pos hc 2012, pow_pos hd 2012]

  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- a^2012 - b^2012 = 0, which contradicts a ≠ b
    exfalso
    have : a^2012 = b^2012 := by linarith
    have : a = b := by
      have h1 : a^2012 = b^2012 := this
      have h2 : a > 0 := ha
      have h3 : b > 0 := hb
      rw [pow_left_inj (by linarith) (by linarith) (by norm_num)] at h1
      linarith
    tauto
  · -- a^2012 + b^2012 = c^2012 + d^2012
    have h5' : a^2012 + b^2012 = c^2012 + d^2012 := by linarith
    nlinarith [h1, h2, h5', pow_pos ha 2012, pow_pos hb 2012, pow_pos hc 2012, pow_pos hd 2012, mul_pos ha hb, mul_pos hc hd, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd]
  all_goals
    nlinarith