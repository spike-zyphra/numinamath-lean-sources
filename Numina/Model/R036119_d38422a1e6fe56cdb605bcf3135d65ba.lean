import Mathlib

theorem algebra_142822 {x : ℝ} (hx : x ≠ 0) :
    (1 - (1 + 1 / x ^ 2) ^ (-1 : ℤ)) ^ (-1 : ℤ) = 3.25 ↔ x = 1.5 ∨ x = -1.5 := by
  constructor
  · -- Assume the equation holds, prove x = 1.5 ∨ x = -1.5
    intro h
    have eq1 : (1 - (1 + 1 / x ^ 2) ^ (-1 : ℤ)) ^ (-1 : ℤ) = x^2 + 1 := by
      simp [zpow_neg_one, zpow_ofNat]
      field_simp [hx]
      <;> ring
    rw [eq1] at h
    have eq2 : x^2 = 2.25 := by
      nlinarith
    have eq3 : x = 1.5 ∨ x = -1.5 := by
      have h1 : x^2 - 2.25 = 0 := by
        linarith
      have h2 : (x - 1.5) * (x + 1.5) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h2) with h3 h4
      · -- h3 : x - 1.5 = 0
        left
        linarith
      · -- h4 : x + 1.5 = 0
        right
        linarith
    exact_mod_cast eq3
  · -- Assume x = 1.5 ∨ x = -1.5, prove the equation
    rintro (h | h)
    · -- h : x = 1.5
      rw [h]
      norm_num [zpow_neg_one, zpow_ofNat]
    · -- h : x = -1.5
      rw [h]
      norm_num [zpow_neg_one, zpow_ofNat]