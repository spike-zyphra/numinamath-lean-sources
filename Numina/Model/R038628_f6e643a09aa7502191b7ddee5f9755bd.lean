import Mathlib

theorem calculus_23100 (θ : ℝ) (k : ℝ) (h : k = Real.sin θ ^ 6 + Real.cos θ ^ 6) (h' : k = Real.sin (2 * θ)) :
    k = 2 / 3 := by
  have h1 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have eq1 : Real.sin θ ^ 6 + Real.cos θ ^ 6 = 1 - 3 * (Real.sin θ * Real.cos θ) ^ 2 := by
    have h2 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := h1
    have h3 : Real.sin θ ^ 6 + Real.cos θ ^ 6 = (Real.sin θ ^ 2 + Real.cos θ ^ 2) ^ 3 - 3 * (Real.sin θ ^ 2) * (Real.cos θ ^ 2) * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by 
      ring
    rw [h3, h2]
    <;> ring
  have hk1 : k = 1 - 3 * (Real.sin θ * Real.cos θ) ^ 2 := by
    rw [h]
    rw [eq1]
  -- From h', k = sin(2θ) = 2 sin θ cos θ
  have hk2 : k = 2 * (Real.sin θ * Real.cos θ) := by
    rw [h']
    have h3 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := by 
      rw [Real.sin_two_mul]
    rw [h3]
    <;> ring
  have eq2 : 3 * (Real.sin θ * Real.cos θ) ^ 2 + 2 * (Real.sin θ * Real.cos θ) - 1 = 0 := by 
    nlinarith [hk1, hk2]
  have eq3 : (Real.sin θ * Real.cos θ - 1 / 3) * (Real.sin θ * Real.cos θ + 1) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp eq3) with h4 h5
  · -- Real.sin θ * Real.cos θ = 1/3 
    have eq5 : Real.sin θ * Real.cos θ = 1 / 3 := by linarith
    nlinarith [hk2, eq5, sq_nonneg (Real.sin θ ^ 2 - Real.cos θ ^ 2)]
  · -- Real.sin θ * Real.cos θ = -1 
    have eq6 : Real.sin θ * Real.cos θ = -1 := by linarith 
    nlinarith [sq_nonneg (Real.sin θ ^ 2 - Real.cos θ ^ 2), sq_nonneg (Real.sin θ * Real.cos θ), sq_nonneg (Real.sin θ ^ 2 - Real.cos θ ^ 2), sq_nonneg (Real.sin θ * Real.cos θ), sq_nonneg (Real.sin θ ^ 2), sq_nonneg (Real.cos θ ^ 2)]