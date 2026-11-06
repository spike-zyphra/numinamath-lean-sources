import Mathlib

theorem algebra_256248 :
  { x : ℝ | x ≥ -1 ∧ Real.sqrt (x + 6) + Real.sqrt (x + 1) = Real.sqrt (7 * x + 4) } =
  { 3 } := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x in the left side
    rintro ⟨hx, heq⟩
    have h1 : x ≥ -1 := hx
    have h2 : x ≥ -1 := h1
    have h3 : 7 * x + 4  ≥ 0 := by
      by_contra h
      push_neg at h
      have h4 : 7 * x + 4 < (0 : ℝ) := by linarith
      have h5 : Real.sqrt (7 * x + 4) = 0 := by
        rw [Real.sqrt_eq_zero'.mpr]
        linarith
        all_goals linarith
      rw [h5] at heq
      have h6 : Real.sqrt (x + 6) + Real.sqrt (x + 1) = (0 : ℝ) := by
        linarith
      have h7 : Real.sqrt (x + 6) ≥ 0 := Real.sqrt_nonneg (x + 6)
      have h8 : Real.sqrt (x + 1) ≥ 0 := Real.sqrt_nonneg (x + 1)
      have h9 : Real.sqrt (x + 6) = 0 := by
        nlinarith
      have h10 : x + 6 = 0 := by
        rw [Real.sqrt_eq_zero (by nlinarith)] at h9
        linarith
      nlinarith
    have h4 : Real.sqrt (x + 6) + Real.sqrt (x + 1) = Real.sqrt (7 * x + 4) := heq
    have eq1 : (Real.sqrt (x + 6) + Real.sqrt (x + 1)) ^ 2 = (Real.sqrt (7 * x + 4)) ^ 2 := by
      rw [h4]
    have eq2 : (Real.sqrt (x + 6) + Real.sqrt (x + 1)) ^ 2 = (Real.sqrt (x + 6)) ^ 2 + (Real.sqrt (x + 1)) ^ 2 + 2 * (Real.sqrt (x + 6) * Real.sqrt (x + 1)) := by ring
    have eq3 : (Real.sqrt (7 * x + 4)) ^ 2 = 7 * x + 4 := Real.sq_sqrt (by nlinarith)
    rw [eq2, eq3] at eq1
    have eq4 : (Real.sqrt (x + 6)) ^ 2 = x + 6 := Real.sq_sqrt (by nlinarith)
    have eq5 : (Real.sqrt (x + 1)) ^ 2 = x + 1 := Real.sq_sqrt (by nlinarith)
    rw [eq4, eq5] at eq1
    have h5 : 2 * (Real.sqrt (x + 6) * Real.sqrt (x + 1)) = 2 * Real.sqrt ((x + 6) * (x + 1)) := by
      have h6 : Real.sqrt ((x + 6) * (x + 1)) = Real.sqrt (x + 6) * Real.sqrt (x + 1) := by
        rw [← Real.sqrt_mul (by nlinarith)]
        all_goals norm_num
      nlinarith [h6]
    rw [h5] at eq1
    have eq6 : 2 * Real.sqrt ((x + 6) * (x + 1)) = 5 * x - 3  := by
      nlinarith [eq1]
    have h8 : x ≥ (3 : ℝ) / 5 := by
      by_contra h
      push_neg at h
      have h5x : x < (3 : ℝ) / 5 := h
      have h9 : 5 * x - 3 < (0 : ℝ) := by
        nlinarith
      have h7 : Real.sqrt ((x + 6) * (x + 1)) ≥ 0 := Real.sqrt_nonneg ((x + 6) * (x + 1))
      nlinarith [Real.sqrt_nonneg ((x + 6) * (x + 1))]
    have eq7 : (2 * Real.sqrt ((x + 6) * (x + 1))) ^ 2 = (5 * x - 3) ^ 2 := by
      rw [eq6]
    have eq8 : (2 * Real.sqrt ((x + 6) * (x + 1))) ^ 2 = 4 * ((x + 6) * (x + 1)) := by
      calc
        (2 * Real.sqrt ((x + 6) * (x + 1))) ^ 2
          = 4 * (Real.sqrt ((x + 6) * (x + 1)) ^ 2) := by ring
        _ = 4 * ((x + 6) * (x + 1)) := by
          rw [Real.sq_sqrt]
          all_goals nlinarith
    have eq9 : (5 * x - 3) ^ 2 = 25 * x ^ 2 - 30 * x + 9 := by ring
    -- Now solve quadratic
    have eq10 : 21 * x ^ 2 - 58 * x - 15 = 0 := by
      nlinarith [eq8, eq9]
    have eq11 : (x - 3) * (21 * x + 5) = 0  := by
      nlinarith
    cases' (mul_eq_zero.mp eq11) with h9 h10
    · -- Case x - 3 = 0
      linarith
    · -- Case 21 * x + 5 = 0
      have h5x : x = -5 / 21  :=  by linarith
      nlinarith [Real.sqrt_nonneg (x + 6), Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (7 * x + 4)]
  · -- Show that 3 is in the left side
    intro heq
    rw [show x = (3 : ℝ) by linarith]
    constructor
    · -- Show 3 ≥ -1
      norm_num
    · -- Show sqrt(3+6) + sqrt(3+1) = sqrt(7*3+4)
      have h1 : Real.sqrt (3 + 6) = (3 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.sqrt (3 + 1) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h3 : Real.sqrt (7 * (3 : ℝ) + 4) = (5 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1, h2, h3]
      all_goals norm_num