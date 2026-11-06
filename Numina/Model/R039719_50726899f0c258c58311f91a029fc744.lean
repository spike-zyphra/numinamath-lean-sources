import Mathlib

theorem algebra_187545 (x : ℝ) (hx : 0 ≤ 3 * x ^ 2 - 5 * x - 4 ∧ 0 ≤ 3 * x ^ 2 - 5 * x - 8) :
    Real.sqrt (3 * x ^ 2 - 5 * x - 4) + Real.sqrt (3 * x ^ 2 - 5 * x - 8) = 2 ↔
    x = 8 / 3 ∨ x = -1 := by
  constructor
  · -- Assume the equation holds, prove x = 8/3 or x = -1
    intro h_eq
    have h1 : 0 ≤ 3 * x ^ 2 - 5 * x - 4 := hx.1
    have h2 : 0 ≤ 3 * x ^ 2 - 5 * x - 8 := hx.2
    have h3 : Real.sqrt (3 * x ^ 2 - 5 * x - 4) ≥ 0 := Real.sqrt_nonneg (3 * x ^ 2 - 5 * x - 4)
    have h4 : Real.sqrt (3 * x ^ 2 - 5 * x - 8) ≥ 0 := Real.sqrt_nonneg (3 * x ^ 2 - 5 * x - 8)
    have eq1 : Real.sqrt (3 * x ^ 2 - 5 * x - 4) + Real.sqrt (3 * x ^ 2 - 5 * x - 8) = 2 := h_eq
    have eq2 : Real.sqrt (3 * x ^ 2 - 5 * x - 4) = 2 - Real.sqrt (3 * x ^ 2 - 5 * x - 8) := by linarith
    have eq3 : (Real.sqrt (3 * x ^ 2 - 5 * x - 4)) ^ 2 = (2 - Real.sqrt (3 * x ^ 2 - 5 * x - 8)) ^ 2 := by
      rw [eq2]
    have eq4 : (Real.sqrt (3 * x ^ 2 - 5 * x - 4)) ^ 2 = 3 * x ^ 2 - 5 * x - 4 := by
      exact Real.sq_sqrt h1
    have eq5 : (2 - Real.sqrt (3 * x ^ 2 - 5 * x - 8)) ^ 2 = 4 - 4 * Real.sqrt (3 * x ^ 2 - 5 * x - 8) + (Real.sqrt (3 * x ^ 2 - 5 * x - 8)) ^ 2 := by
      ring
    have eq6 : (Real.sqrt (3 * x ^ 2 - 5 * x - 8)) ^ 2 = 3 * x ^ 2 - 5 * x - 8 := by
      exact Real.sq_sqrt h2
    rw [eq4, eq5, eq6] at eq3
    have eq7 : Real.sqrt (3 * x ^ 2 - 5 * x - 8) = 0 := by
      nlinarith
    have eq8 : 3 * x ^ 2 - 5 * x - 8 = 0 := by
      have h7 : Real.sqrt (3 * x ^ 2 - 5 * x - 8) = 0 := eq7
      have h8 : (Real.sqrt (3 * x ^ 2 - 5 * x - 8)) ^ 2 = 0 := by
        rw [h7]
        all_goals norm_num
      nlinarith [Real.sq_sqrt h2]
    have eq9 : (x - 8 / 3) * (x + 1) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.mp eq9) with h10 h11
    · -- Case x - 8/3 = 0
      left
      linarith
    · -- Case x + 1 = 0
      right
      linarith
  · -- Assume x = 8/3 or x = -1, prove the equation
    rintro (h | h)
    · -- Case x = 8/3
      have h1 : x = 8 / 3 := h
      have hx1 : 3 * x ^ 2 - 5 * x - 4 = 4 := by 
        rw [h1]
        norm_num
      have hx2 : 3 * x ^ 2 - 5 * x - 8 = 0 := by 
        rw [h1]
        norm_num
      have h3 : Real.sqrt (3 * x ^ 2 - 5 * x - 4) = 2 := by 
        rw [hx1]
        exact Real.sqrt_eq_cases.2 (by norm_num)
      have h4 : Real.sqrt (3 * x ^ 2 - 5 * x - 8) = 0 := by 
        rw [hx2]
        exact Real.sqrt_eq_zero'.mpr (by norm_num)
      rw [h3, h4]
      all_goals norm_num
    · -- Case x = -1
      have h2 : x = -1 := h
      have hx1 : 3 * x ^ 2 - 5 * x - 4 = 4 := by 
        rw [h2]
        norm_num
      have hx2 : 3 * x ^ 2 - 5 * x - 8 = 0 := by 
        rw [h2]
        norm_num
      have h3 : Real.sqrt (3 * x ^ 2 - 5 * x - 4) = 2 := by 
        rw [hx1]
        exact Real.sqrt_eq_cases.2 (by norm_num)
      have h4 : Real.sqrt (3 * x ^ 2 - 5 * x - 8) = 0 := by 
        rw [hx2]
        exact Real.sqrt_eq_zero'.mpr (by norm_num)
      rw [h3, h4]
      all_goals norm_num