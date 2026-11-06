import Mathlib

theorem algebra_206605 (x : ℝ) (hx : x ≥ 1) :
    Real.sqrt (x + 2 * Real.sqrt (x - 1)) + Real.sqrt (x - 2 * Real.sqrt (x - 1)) = 2 ↔
    1 ≤ x ∧ x ≤ 2 := by
  have h1 : x - 1 ≥ 0 := by linarith
  have h2 : x + 2 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) + 1) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
  have h3 : x - 2 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 1) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
  have h4 : Real.sqrt (x + 2 * Real.sqrt (x - 1)) = Real.sqrt (x - 1) + 1 := by
    rw [h2]
    have h5 : Real.sqrt ((Real.sqrt (x - 1) + 1) ^ 2) = Real.sqrt (x - 1) + 1 := by
      rw [Real.sqrt_sq (show Real.sqrt (x - 1) + 1 ≥ 0 by positivity)]
    linarith [h5]
  by_cases h5 : x - 1 ≥ 1
  · -- Assume x - 1 >= 1, that is, x >= 2
    have h7 : Real.sqrt (x - 1) ≥ 1 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h8 : Real.sqrt (x - 2 * Real.sqrt (x - 1)) = Real.sqrt (x - 1) - 1 := by
      rw [h3]
      have h9 : Real.sqrt ((Real.sqrt (x - 1) - 1) ^ 2) = Real.sqrt (x - 1) - 1 := by
        rw [Real.sqrt_sq (show Real.sqrt (x - 1) - 1 ≥ 0 by nlinarith)]
      linarith [h9]
    rw [h4, h8]
    constructor
    · -- Assume sqrt(x -1) +1 + sqrt(x -1) -1 = 2 => 2 sqrt(x-1) = 2
      intro h
      have h8 : Real.sqrt (x - 1) = 1 := by
        linarith
      have h9 : x - 1 = 1 := by
        calc
          x - 1 = (Real.sqrt (x - 1)) ^ 2 := by rw [Real.sq_sqrt (by linarith)]
          _ = 1 ^ 2 := by rw [h8]
          _ = 1 := by norm_num
      have h10 : x = 2 := by linarith
      constructor <;> linarith
    · -- Assume 1 <=x <=2, so x =2 in this case
      rintro ⟨h10, h11⟩
      have h10 : x = 2 := by linarith
      rw [h10]
      -- Substitute x=2. First sqrt becomes sqrt(2+2*sqrt(2-1)) = sqrt(2+2*1)= sqrt(4)=2
      -- Second sqrt sqrt(2-2*sqrt(2-1))= sqrt(2-2*1) = sqrt(0)=0
      have h8 : Real.sqrt (2 - 1) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h9 : Real.sqrt (2 + 2 * Real.sqrt (2 - 1)) = 2 := by
        rw [h8]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h10 : Real.sqrt (2 - 2 * Real.sqrt (2 - 1)) = 0 := by
        rw [h8]
        rw [Real.sqrt_eq_zero'] <;> norm_num
      linarith [h9, h10]
  · -- Assume x - 1 <1 => 1 <= x <2
    have h7 : Real.sqrt (x - 1) < 1 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    have h8 : Real.sqrt (x - 2 * Real.sqrt (x - 1)) = 1 - Real.sqrt (x - 1) := by
      rw [h3]
      have h9 : Real.sqrt ((Real.sqrt (x - 1) - 1) ^ 2) = 1 - Real.sqrt (x - 1) := by
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_neg (by nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)])]
        all_goals nlinarith
      linarith [h9]
    rw [h4, h8]
    constructor
    · -- Assume equality holds
      intro h
      constructor <;> linarith
    · -- Assume right side holds
      rintro ⟨h10, h11⟩
      linarith