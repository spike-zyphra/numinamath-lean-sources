import Mathlib

theorem algebra_21387 {a b c : ℝ} (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a = b) (h₄ : c = a * Real.sqrt 2) (h₅ : 6 = (a * b) / c) :
    (1 / 2) * a * b = 36 := by

  have h6 : a = b := h₃
  have h7 : c = a * Real.sqrt 2 := h₄

  rw [h6] at h₅
  rw [h7] at h₅
  
  have h8 : Real.sqrt 2 > 0 := by positivity
  have h9 : a * Real.sqrt 2 > 0 := mul_pos h₀ h8
  
  have eq1 : a * a = 6 * (a * Real.sqrt 2) := by
    have h_eq : (a * a) / (a * Real.sqrt 2) = 6 := by
      field_simp at h₅ ⊢
      nlinarith
    have h_zero : a * a - 6 * (a * Real.sqrt 2) = 0 := by
      field_simp at h_eq ⊢
      nlinarith
    linarith

  have h14 : a * (a - 6 * Real.sqrt 2) = 0 := by
    ring_nf at eq1 ⊢
    linarith
  
  cases' (mul_eq_zero.mp h14) with h15 h16
  · -- Case $h15: a = 0$, contradicts with $a > 0$.
    linarith
  · -- Case $h16: a - 6 * \sqrt{2} = 0$, so $a = 6 * \sqrt{2}$.
    have h16' : a = 6 * Real.sqrt 2 := by
      linarith

    have h7 : b = 6 * Real.sqrt 2 := by
      rw [show b = a by linarith [h6]]
      linarith [h16']

    have h18 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)

    have : (1 / 2) * a * b = 36 := by
      rw [show a = 6 * Real.sqrt 2 by linarith [h16'], show b = 6 * Real.sqrt 2 by linarith [h7]]
      ring_nf
      have h19 : (Real.sqrt 2) ^ 2 = 2 := h18
      rw [h19]
      norm_num
      <;> ring_nf <;> norm_num

    linarith