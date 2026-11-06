import Mathlib

theorem algebra_182986 {a b c : ℝ} (h₀ : a^2 - b * c = 14) (h₁ : b^2 - c * a = 14) (h₂ : c^2 - a * b = -3) :
    |a + b + c| = 17 / 5 := by
  have h3 : (a - b) * (a + b + c) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- case $a - b = 0$, so $a = b$
    have ha : a = b := by linarith
    have eq1 : a^2 - a * c = 14 := by
      rw [show b = a by linarith [ha] ] at h₀
      nlinarith
    have eq2 : c^2 - a^2 = -3 := by
      rw [show b = a by linarith [ha] ] at h₂
      nlinarith
    have h8 : a^2 = c^2 + 3 := by linarith
    have h9 : a * c = c^2 - 11 := by
      nlinarith
    have h10 : c^2 = 121 / 25 := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (a + c), sq_nonneg (c)]
    have hc1 : c = 11 / 5 ∨ c = -11 / 5 := by
      have h20 : c^2 - (121 / 25) = 0 := by linarith
      have h21 : (c - 11 / 5) * (c + 11 / 5) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h21) with h22 h23
      · -- c - 11/5 = 0
        left
        linarith
      · -- c + 11/5 = 0
        right
        linarith
    cases' hc1 with hc11 hc11
    · -- c = 11/5, so $a = -14/5$
      have h6a : a = -14 / 5 := by
        rw [hc11] at h9
        nlinarith
      have h7a : a + b + c = -17 / 5 := by
        nlinarith [ha, h6a, hc11]
      rw [h7a]
      norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- c = -11/5, so $a = 14/5$
      have h6a : a = 14 / 5 := by
        rw [hc11] at h9
        nlinarith
      have h7a : a + b + c = 17 / 5 := by
        nlinarith [ha, h6a, hc11]
      rw [h7a]
      norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- case a + b + c = 0
    have h6 : c = -a - b := by linarith
    rw [show c = -a - b by linarith] at h₀ h₁ h₂
    nlinarith