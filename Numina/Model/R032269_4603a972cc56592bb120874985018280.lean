import Mathlib

theorem algebra_218147 (f : ℝ → ℝ) (hf : f = fun x => Real.sqrt (x + 3) + Real.sqrt (3 * x - 2) - 7) :
    ∃! x, f x = 0 := by
  use 6
  constructor
  · -- Show that f 6 = 0.
    rw [hf]
    have h1 : Real.sqrt (6 + 3) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (3 * (6 : ℝ) - 2) = 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    simp only [h1, h2]
    all_goals norm_num
  · -- Show that for any x, f x = 0 implies x = 6.
    intro x hx
    rw [hf] at hx
    simp at hx
    have h1 : 0 ≤ x + 3 := by
      by_contra h
      push_neg at h
      have h2 : x + 3 < 0 := by linarith
      have h3 : Real.sqrt (x + 3) = 0 := by
        rw [Real.sqrt_eq_zero'.mpr]
        linarith
      have h4 : Real.sqrt (3 * x - 2) = 7 := by
        nlinarith [h3, hx]
      by_contra h6
      push_neg at h6
      have h7 : 3 * x - 2 < 0 := by nlinarith
      have h8 : Real.sqrt (3 * x - 2) = 0 := by
        rw [Real.sqrt_eq_zero'.mpr]
        linarith
      nlinarith [h4, h8]
    have h2 : 0 ≤ 3 * x - 2 := by
      by_contra h
      push_neg at h
      have h3 : 3 * x - 2 < 0 := by linarith
      have h4 : Real.sqrt (3 * x - 2) = 0 := by
        rw [Real.sqrt_eq_zero'.mpr]
        linarith
      have  h5 : Real.sqrt (x + 3) = 7 := by
        nlinarith [h4, hx]
      have h6 : 0 ≤ (x + 3 : ℝ) := by linarith
      have h7 : (Real.sqrt (x + 3)) ^ 2 = (7 : ℝ) ^ 2 := by
        rw [h5]
      have h8 : (Real.sqrt (x + 3)) ^ 2 = x + 3 := by
        exact Real.sq_sqrt (by linarith)
      nlinarith
    have h3 : Real.sqrt (x + 3) ≥ 0 := Real.sqrt_nonneg (x + 3)
    have h4 : Real.sqrt (3 * x - 2) ≥ 0 := Real.sqrt_nonneg (3 * x - 2)
    have h5 : (Real.sqrt (x + 3) + Real.sqrt (3 * x - 2)) ^ 2 = (7 : ℝ) ^ 2 := by
      nlinarith [hx]
    have h6 : (Real.sqrt (x + 3) + Real.sqrt (3 * x - 2)) ^ 2 = 
        (Real.sqrt (x + 3)) ^ 2 + (Real.sqrt (3 * x - 2)) ^ 2 + 2 * (Real.sqrt (x + 3) * Real.sqrt (3 * x - 2)) := by ring
    rw [h6] at h5
    have h7 : (Real.sqrt (x + 3)) ^ 2 = x + 3 := Real.sq_sqrt (by linarith)
    have h8 : (Real.sqrt (3 * x - 2))  ^ 2 = 3 * x - 2 := Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (3 * x - 2), Real.sq_sqrt (show (0 : ℝ) ≤ (x + 3) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 * x - 2) by nlinarith)]