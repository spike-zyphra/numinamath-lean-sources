import Mathlib

theorem algebra_3219 {a b c : ℤ} (h₀ : a + b + c = 0) (h₁ : a ^ 2 + b ^ 2 + c ^ 2 ≠ 0)
    (h₂ : a ^ 3 + b ^ 3 + c ^ 3 = 0) :
    a ^ 2021 + b ^ 2021 + c ^ 2021 = 0 := by

  have h3 : a * b * c = 0 := by
    have h4 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) =
        (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + a * c + b * c)) := by
      ring
    rw [h₀] at h4 
    have h5 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = 0 := by linarith [h4] 
    have h6 : a * b * c = 0 := by linarith [h₂, h5]
    linarith
  cases' (mul_eq_zero.mp h3) with h4 h5
  cases' (mul_eq_zero.mp h4) with h6 h7
  · -- When a = 0
    have ha : a = 0 := by
      linarith 
    have hc : c = -b := by
      linarith [ha, h₀]
    rw [ha, hc]
    ring_nf
    <;> norm_num
  · -- When b = 0
    have hb : b = 0 := by
      linarith 
    have hc : c = -a := by
      linarith [hb, h₀]
    rw [hb, hc]
    ring_nf
    <;> norm_num
  · -- When c = 0
    have hc : c = 0 := by
      linarith 
    have hb : b = -a := by
      linarith [hc, h₀]
    rw [hb, hc]
    ring_nf
    <;> norm_num