import Mathlib

theorem algebra_8937 {x : ℝ} (hx : x ≥ 0) (hx1 : x^2 - x + 1 > 0) :
    (3 * x + 3) / Real.sqrt x - (x + 1) / Real.sqrt (x^2 - x + 1) = 4 ↔ x = 1 := by
  constructor
  · -- Forward direction: If the equation holds, then x = 1.
    intro h_eq
    by_cases h1 : x = 0
    · -- If x = 0, the equation is invalid because of division by zero
      rw [h1] at h_eq
      norm_num [Real.sqrt_eq_zero] at h_eq
      all_goals linarith
    · -- x > 0
      have hx2 : x > 0 := by
        by_contra h
        push_neg at h
        have h1' : x = 0 := by linarith
        tauto
      have h2 : Real.sqrt x > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      have h3 : Real.sqrt (x^2 - x + 1) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      have eq1 : (3 * x + 3) / Real.sqrt x - (x + 1) / Real.sqrt (x^2 - x + 1) =
        ((3 * x + 3) * Real.sqrt (x^2 - x + 1) - (x + 1) * Real.sqrt x) / (Real.sqrt x * Real.sqrt (x^2 - x + 1)) := by
        field_simp [h2, h3]
        <;> ring
      rw [eq1] at h_eq
      have h4 : Real.sqrt x * Real.sqrt (x^2 - x + 1) > 0 := by
        positivity
      have eq2 : (3 * x + 3) * Real.sqrt (x^2 - x + 1) - (x + 1) * Real.sqrt x = 4 * (Real.sqrt x * Real.sqrt (x^2 - x + 1)) := by
        field_simp [h4] at h_eq ⊢
        linarith
      have eq3 : Real.sqrt (x ^ 2 - x + 1) = Real.sqrt x := by
        nlinarith [sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt (x^2 - x + 1) - 1),
            Real.sqrt_nonneg x, Real.sqrt_nonneg (x^2 - x + 1),
            Real.sq_sqrt (show x ≥ 0 by linarith), Real.sq_sqrt (show x ^ 2 - x + 1 ≥ 0 by nlinarith),
            Real.sqrt_nonneg (x ^ 2 - x + 1), Real.sqrt_nonneg x,
            sq_nonneg (Real.sqrt (x ^ 2 - x + 1) - Real.sqrt x)
          ]
      have eq4 : x ^ 2 - x + 1 = x := by
        calc
          x ^ 2 - x + 1 = (Real.sqrt (x ^ 2 - x + 1)) ^ 2 := by
            rw [Real.sq_sqrt]
            nlinarith
          _ = (Real.sqrt x) ^ 2 := by
            rw [eq3]
          _ = x := by
            rw [Real.sq_sqrt]
            nlinarith
      have eq5 : (x - 1) ^ 2 = 0 := by
        nlinarith
      have eq6 : x - 1 = 0 := by
        apply pow_eq_zero
        exact eq5
      linarith
  · -- Reverse direction: x = 1 implies the equation holds
    intro h_eq
    rw [h_eq]
    have h2 : Real.sqrt (1 : ℝ) = (1 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h2]
    have h1 : Real.sqrt ((1 : ℝ) ^ 2 - (1 : ℝ) + 1) = (1 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
    all_goals norm_num