import Mathlib

theorem algebra_186793 (x : ℝ) (hx : 4 ≤ x) :
    Real.sqrt (3 * x + 4) + Real.sqrt (x - 4) = 2 * Real.sqrt x ↔ x = 4 := by
  constructor
  · -- Forward direction: if the equation holds, then x = 4.
    intro h_eq
    have h7 : Real.sqrt (3 * x + 4) ≥ 0 := by positivity
    have h8 : Real.sqrt (x - 4) ≥ 0 := by positivity
    have h9 : Real.sqrt x ≥ 0 := by positivity

    have eq1 : (Real.sqrt (3 * x + 4) + Real.sqrt (x - 4)) ^ 2 = (2 * Real.sqrt x) ^ 2 := by
      rw [h_eq]

    have eq2 : (Real.sqrt (3 * x + 4) + Real.sqrt (x - 4)) ^ 2 = (Real.sqrt (3 * x + 4)) ^ 2 + (Real.sqrt (x - 4)) ^ 2 + 2 * (Real.sqrt (3 * x + 4) * Real.sqrt (x - 4)) := by ring

    have eq3 : (2 * Real.sqrt x) ^ 2 = 4 * Real.sqrt x ^ 2 := by ring

    have h4 : Real.sqrt (3 * x + 4) ^ 2 = 3 * x + 4 := by
      have h1 : 3 * x + 4 ≥ 0 := by linarith
      exact Real.sq_sqrt h1

    have h5 : Real.sqrt (x - 4) ^ 2 = x - 4 := by
      have h2 : x - 4 ≥ 0 := by linarith
      exact Real.sq_sqrt h2

    have h6 : Real.sqrt x ^ 2 = x := by
      have h3 : x ≥ 0 := by linarith
      exact Real.sq_sqrt h3

    rw [eq2, eq3, h4, h5, h6] at eq1

    have eq4 : Real.sqrt (3 * x + 4) * Real.sqrt (x - 4) = 0 := by
      nlinarith

    have h10 : Real.sqrt (3 * x + 4) = 0 ∨ Real.sqrt (x - 4) = 0 := by
      cases (mul_eq_zero.1 eq4) with
      | inl h => 
          left
          nlinarith
      | inr h => 
          right
          nlinarith

    cases h10 with
    | inl h11 =>
      -- Case where sqrt(3x + 4) = 0, implying 3x + 4 = 0, which contradicts x >= 4
      have h14 : 3 * x + 4 = 0 := by
        have h7 : Real.sqrt (3 * x + 4) = 0 := h11
        have h8 : 3 * x + 4 ≥ 0 := by nlinarith
        rw [Real.sqrt_eq_zero (by linarith)] at h7
        linarith

      nlinarith
    | inr h12 =>
      -- Case where sqrt(x - 4) = 0, implying x - 4 = 0, so x = 4
      have h13 : x - 4 = 0 := by
        have h8 : Real.sqrt (x - 4) = 0 := h12
        have h9 : x - 4 ≥ 0 := by nlinarith
        rw [Real.sqrt_eq_zero (by linarith)] at h8
        linarith

      linarith
  · -- Backward direction: x = 4 implies the equation
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt (3 * (4 : ℝ) + 4) = 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (4 - 4 : ℝ) = 0 := by
      norm_num [Real.sqrt_eq_iff_sq_eq]
    have h3 : Real.sqrt (4 : ℝ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3]
    all_goals norm_num