import Mathlib

theorem algebra_289419 (θ : ℝ) (h : (1 - Real.cos θ) / (4 + Real.sin θ ^ 2) = 1 / 2) :
    (4 + Real.cos θ ^ 3) * (3 + Real.sin θ ^ 3) = 9 := by

  have h1 : 4 + Real.sin θ ^ 2 ≠ 0 := by
    have h2 : Real.sin θ ^ 2 ≥ 0 := sq_nonneg (Real.sin θ)
    nlinarith
  
  have eq1 : 2 * (1 - Real.cos θ) = 4 + Real.sin θ ^ 2 := by
    field_simp [h1] at h
    nlinarith
  
  have eq2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    have h3 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    linarith
  
  have quad_eq : Real.cos θ ^ 2 - 2 * Real.cos θ - 3 = 0 := by
    rw [eq2] at eq1
    nlinarith
  
  have cos_val : Real.cos θ = -1 := by
    have h7 : (Real.cos θ + 1) * (Real.cos θ - 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h7) with h8 h9
    · -- Real.cos θ + 1 = 0, so Real.cos θ = -1
      linarith
    · -- Real.cos θ - 3 = 0, so Real.cos θ = 3, impossible
      have h10 : Real.cos θ ≤ 1 := Real.cos_le_one θ
      nlinarith
  
  have sin_val : Real.sin θ = 0 := by
    have h6 : Real.cos θ = -1 := cos_val
    have h7 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [h6] at h7
    have h8 : Real.sin θ ^ 2 = 0 := by nlinarith
    have h9 : Real.sin θ = 0 := by
      nlinarith
    exact h9
  
  rw [cos_val, sin_val]
  norm_num