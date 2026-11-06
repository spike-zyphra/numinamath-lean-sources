import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_78567 :
  IsGreatest {k : ℝ | ∃ x : ℝ, 0 ≤ x - 3 ∧ 0 ≤ 6 - x ∧ sqrt (x - 3) + sqrt (6 - x) ≥ k} (sqrt 6) := by 
  constructor
  · -- Show that sqrt 6 belongs to the set
    use (9 / 2 : ℝ)
    constructor
    · norm_num 
    constructor
    · norm_num
    · -- Show that sqrt (9/2 - 3) + sqrt (6 - 9/2) ≥ sqrt 6
      have h1 : Real.sqrt ((9 / 2 : ℝ) - 3) = Real.sqrt (3 / 2 : ℝ) := by norm_num
      have h2 : Real.sqrt ((6 : ℝ) - (9 / 2 : ℝ)) = Real.sqrt (3 / 2 : ℝ) := by norm_num
      rw [h1, h2]
      have h3 : Real.sqrt (3 / 2 : ℝ) = Real.sqrt 6 / 2 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h3]
      have h4 : Real.sqrt 6 / 2 + Real.sqrt 6 / 2 = Real.sqrt 6 := by ring_nf
      linarith [h4, Real.sqrt_nonneg 6]
  · -- Show that sqrt 6 is the greatest element in the set
    intro k hk
    rcases hk with ⟨x, hx1, hx2, h⟩
    have h1 : sqrt (x - 3) + sqrt (6 - x) ≤ sqrt 6 := by
      have h4 : (sqrt (x - 3) + sqrt (6 - x)) ^ 2 ≤ (6 : ℝ) := by
        have h5 : (sqrt (x - 3) + sqrt (6 - x)) ^ 2 = (sqrt (x - 3)) ^ 2 + (sqrt (6 - x)) ^ 2 + 2 * (sqrt (x - 3) * sqrt (6 - x)) := by ring
        rw [h5]
        have h6 : (sqrt (x - 3)) ^ 2 = x - 3 := Real.sq_sqrt (by linarith)
        have h7 : (sqrt (6 - x)) ^ 2 = 6 - x := Real.sq_sqrt (by linarith)
        have h8 : sqrt (x - 3) * sqrt (6 - x) = sqrt ((x - 3) * (6 - x)) := by
          rw [← Real.sqrt_mul (by nlinarith)]
          all_goals nlinarith
        have h9 : sqrt ((x - 3) * (6 - x)) ≤ sqrt (2.25 : ℝ) := by
          apply Real.sqrt_le_sqrt
          nlinarith [sq_nonneg (x - 4.5)]
        have h10 : sqrt (2.25 : ℝ) = 1.5 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf <;> norm_num
        have h11 : sqrt (x - 3) * sqrt (6 - x) ≤ (1.5 : ℝ) := by
          nlinarith [h8, h9, h10, Real.sqrt_nonneg ((x - 3) * (6 - x)), Real.sqrt_nonneg (x - 3), Real.sqrt_nonneg (6 - x)]
        nlinarith [Real.sqrt_nonneg (x - 3), Real.sqrt_nonneg (6 - x), Real.sqrt_nonneg (6 : ℝ), sq_nonneg (sqrt (x - 3) + sqrt (6 - x)), 
                  sq_nonneg (sqrt 6), Real.sq_sqrt (show (0 : ℝ) ≤ (x - 3) by linarith), 
                  Real.sq_sqrt (show (0 : ℝ) ≤ (6 - x) by linarith), 
                  Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by nlinarith)]
      have h2 : sqrt 6 ≥ 0 := by positivity
      have h3 : sqrt (x - 3) + sqrt (6 - x) ≥ 0 := by positivity
      nlinarith [Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), h4, sq_nonneg (sqrt (x - 3) + sqrt (6 - x) - sqrt 6), 
                Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
                sq_nonneg (sqrt (x - 3) - sqrt (6 - x)), sq_nonneg (x - 4.5)]
    linarith [Real.sqrt_nonneg 6, h1, h, Real.sqrt_nonneg (x - 3), Real.sqrt_nonneg (6 - x)]