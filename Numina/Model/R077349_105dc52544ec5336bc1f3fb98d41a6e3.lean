import Mathlib

theorem algebra_118 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h₀ : 1 / a + 1 / b = 9)
    (h₁ : 2 * (1 / a) = 4 * (1 / b) - 12) :
    a = 0.25 ∧ b = 0.2 := by
  have h2 : b + a = 9 * a * b := by
    field_simp at h₀
    nlinarith
  have h3 : 2 * b = 4 * a - 12 * a * b := by
    field_simp at h₁
    nlinarith
  have h5' : a + b = 9 * a * b := by linarith [h2]
  have h6 : (a - 0.25) * (b - 0.2) = 0 := by 
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_pos_of_ne_zero (show b ≠ 0 by exact hb), sq_nonneg (a - 0.25), sq_nonneg (b - 0.2)]
  
  cases' (mul_eq_zero.1 h6) with h7 h8
  · -- case where a = 0.25, so from h5 we derive b = 0.2
    have ha_eq : a = (0.25 : ℝ) := by linarith 
    have hb_eq : b = (0.2 : ℝ) := by
      rw [ha_eq] at h5' 
      nlinarith [sq_pos_of_ne_zero (show b ≠ 0 by exact hb) ]
    constructor
    · linarith
    · linarith
  · -- case where b = 0.2, so from h5 we derive a = 0.25
    have hb_eq : b = (0.2 : ℝ) := by linarith 
    have ha_eq : a = (0.25 : ℝ) := by
      rw [hb_eq] at h5' 
      nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha) ]
    constructor
    · linarith
    · linarith