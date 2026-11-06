import Mathlib

theorem algebra_196987 (x : ℝ) (hx : Real.sin x ≠ 0) (h : Real.sin (3 * x) / Real.sin x = 6 / 5) :
    Real.sin (5 * x) / Real.sin x = -0.76 := by 
  have h1 : Real.sin (3 * x) = 3 * Real.sin x - 4 * Real.sin x ^ 3 := by 
    rw [Real.sin_three_mul]
  have eq1 : Real.sin (3 * x) / Real.sin x = 3 - 4 * Real.sin x ^ 2 := by 
    rw [h1]
    have h2 : Real.sin x ≠ 0 := hx
    field_simp [h2]
    <;> ring
  have h2 : Real.sin (3 * x) / Real.sin x = 6 / 5 := h 
  rw [eq1] at h2 
  have h3 : Real.sin x ^ 2 = 9 / 20 := by 
    nlinarith 
  have eq5 : Real.sin (5 * x) = 16 * Real.sin x ^ 5 - 20 * Real.sin x ^ 3 + 5 * Real.sin x := by
    have h71 : Real.sin (5 * x) = Real.sin (2 * x + 3 * x) := by ring_nf
    rw [h71]
    have h72 : Real.sin (2 * x + 3 * x) = Real.sin (2 * x) * Real.cos (3 * x) + Real.cos (2 * x) * Real.sin (3 * x) := by 
      rw [Real.sin_add]
    rw [h72]
    have h81 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by 
      rw [Real.sin_two_mul]
    have h82 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := by 
      rw [Real.cos_two_mul]
    have h83 : Real.sin (3 * x) = 3 * Real.sin x - 4 * Real.sin x ^ 3 := by
      rw [Real.sin_three_mul]
    rw [h81, h82, h83]
    have hcos : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by 
      have h28 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      linarith
    have h84 : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := hcos
    have h85 : Real.cos x ^ 3 = (1 - Real.sin x ^ 2) * Real.cos x := by 
      calc 
        Real.cos x ^ 3 = Real.cos x ^ 2 * Real.cos x := by ring 
        _ = (1 - Real.sin x ^ 2) * Real.cos x := by rw [h84]
    have h86 : Real.cos (3 * x) = 4 * Real.cos x ^ 3 - 3 * Real.cos x := by 
      rw [Real.cos_three_mul]
    rw [h86, h85]
    have h9 : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq x]
    simp [h9, pow_two, pow_succ, mul_add, add_mul] 
    <;> ring_nf
    <;> simp [pow_three, h9]
    <;> ring_nf
    <;> nlinarith [ sq_nonneg (Real.sin x ^ 2 - 9 / 20) ]
  have eq6 : Real.sin (5 * x) / Real.sin x = 16 * Real.sin x ^ 4 - 20 * Real.sin x ^ 2 + 5 := by
    rw [eq5]
    have h5 : Real.sin x ≠ 0 := hx
    field_simp [h5]
    <;> ring_nf 
  rw [eq6]
  have h41 : Real.sin x ^ 4 = (81 / 400 : ℝ) := by
    calc
      Real.sin x ^ 4 = (Real.sin x ^ 2) ^ 2 := by ring_nf 
      _ = (9 / 20) ^ 2 := by rw [h3]
      _ = (81 / 400 : ℝ) := by norm_num
  rw [show Real.sin x ^ 4 = (81 / 400 : ℝ) by linarith [h41], show Real.sin x ^ 2 = (9 / 20 : ℝ) by linarith [h3]]
  norm_num