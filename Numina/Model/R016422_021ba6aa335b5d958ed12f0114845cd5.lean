import Mathlib

theorem algebra_96356 (a c : ℝ) (ha : a ≠ 0) (h : (2 * Real.sqrt 2) ^ 2 - 4 * a * c = 0) :
    ∃! x : ℝ, a * x ^ 2 - 2 * x * Real.sqrt 2 + c = 0 := by
  have h1 : (2 * Real.sqrt 2) ^ 2 = 8 := by
    calc
      (2 * Real.sqrt 2) ^ 2 = 4 * (Real.sqrt 2) ^ 2 := by ring
      _ = 4 * (2 : ℝ) := by rw [Real.sq_sqrt]; positivity
      _ = (8 : ℝ) := by norm_num

  have h2 : 4 * a * c = 8 := by
    nlinarith [h, h1]

  have h3 : a * c = 2 := by
    nlinarith
  use Real.sqrt 2 / a
  constructor
  · -- First, show that $\sqrt{2}/a$ is indeed a root
    field_simp [ha]
    <;> nlinarith [h3, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Now show that any root must be equal to $\sqrt{2}/a$
    intro x hx
    have h4 : a * x ^ 2 - 2 * x * Real.sqrt 2 + c = 0 := hx
    have h5 : a * x ^ 2 - 2 * x * Real.sqrt 2 + c = 0 := h4
    have h6 : c = 2 / a := by
      field_simp [ha]
      nlinarith [h3]
    rw [h6] at h5
    have h7 : a * x ^ 2 - 2 * x * Real.sqrt 2 + (2 / a) = 0 := h5
    have h8 : a * (a * x ^ 2 - 2 * x * Real.sqrt 2 + (2 / a)) = a * 0 := by
      rw [h7]
      all_goals norm_num
    have h9 : a * (a * x ^ 2 - 2 * x * Real.sqrt 2 + (2 / a)) = a ^ 2 * x ^ 2 - 2 * a * x * Real.sqrt 2 + 2 := by
      field_simp [ha]
      <;> ring
      all_goals norm_num
    rw [h9] at h8
    have h10 : a ^ 2 * x ^ 2 - 2 * a * x * Real.sqrt 2 + 2 = 0 := by
      linarith
    have h11 : (a * x - Real.sqrt 2) ^ 2 = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h12 : a * x - Real.sqrt 2 = 0 := by
      apply pow_eq_zero 
      exact h11
    have h13 : a * x = Real.sqrt 2 := by
      linarith
    have h14 : x = Real.sqrt 2 / a := by
      field_simp [ha]
      <;> nlinarith
    exact h14