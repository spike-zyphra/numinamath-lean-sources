import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_248433 (f : ℝ → ℝ) (hf : f = λ x => abs (x^2 - 4) - 3 * x) :
    image f (Icc (-2) 5) = Icc (-6) (25/4) := by 
  ext y
  simp only [hf, Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc]
  constructor 
  · -- Assume y ∈ f '' (Icc (-2) 5), we need y ∈ Icc (-6) (25/4).
    rintro ⟨x, hx, rfl⟩ -- get the witness x with its bounds and the equality
    rcases hx with ⟨hx1, hx2⟩
    by_cases h1 : x ^ 2 - 4 ≥ 0
    · -- Case where x^2 - 4 ≥ 0, so |x^2 - 4| = x^2 - 4.
      have h2 : abs (x ^ 2 - 4) = x ^ 2 - 4 := by 
        rw [abs_of_nonneg h1]
      rw [h2] -- Replace abs expression 
      constructor 
      · -- Show -6 ≤ x ^ 2 - 4 - 3 * x 
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 5), sq_nonneg (x - 3 / 2)]
      · -- Show x ^ 2 - 4 - 3 * x ≤ 25 / 4 
        nlinarith [sq_nonneg (x - 5 / 2), sq_nonneg (x - 5), sq_nonneg (x - 2)]
    · -- Case where x ^ 2 - 4 < 0, so |x^2 - 4| = 4 - x^2
      have h2 : abs (x ^ 2 - 4) = 4 - x ^ 2 := by 
        rw [abs_of_neg (show x ^ 2 - 4 < (0 : ℝ) by nlinarith)]
        all_goals nlinarith
      rw [h2] -- Replace abs expression
      constructor 
      · -- Show -6 ≤ 4 - x ^ 2 - 3 * x 
        nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 2), sq_nonneg (x - (-3 / 2))]
      · -- Show 4 - x ^ 2 - 3 * x ≤ 25 / 4 
        nlinarith [sq_nonneg (x - (-3 / 2)), sq_nonneg (x + 2), sq_nonneg (x - 2)]
  · -- Assume y ∈ Icc (-6) (25 / 4) need to prove y ∈ f '' (Icc (-2) 5)
    rintro ⟨hy1, hy2⟩ -- Assume y \in [-6, 25/4]
    by_cases h3 : y ≤ 25 / 4 
    · -- Case y ≤ 25 / 4. We can solve using x in [-2, 2]
      use (-3 + Real.sqrt (25 - 4 * y)) / 2 
      constructor 
      · -- Show x ∈ Icc (-2) 5 
        constructor 
        · -- Show -2 ≤ x 
          nlinarith [Real.sqrt_nonneg (25 - 4 * y), Real.sq_sqrt (show (25 - 4 * y : ℝ) ≥ 0 by linarith)]
        · -- Show x ≤ 5 
          nlinarith [Real.sqrt_nonneg (25 - 4 * y), Real.sq_sqrt (show (25 - 4 * y : ℝ) ≥ 0 by linarith)]
      · -- Show f(x) = y.
        have hx2_0 : (-3 + Real.sqrt (25 - 4 * y)) / 2 ≤ (2 : ℝ) := by 
          nlinarith [Real.sqrt_nonneg (25 - 4 * y), Real.sq_sqrt (show (25 - 4 * y : ℝ) ≥ 0 by linarith)]
        have hx2_1 : (-3 + Real.sqrt (25 - 4 * y)) / 2 ≥ (-2 : ℝ) := by 
          nlinarith [Real.sqrt_nonneg (25 - 4 * y), Real.sq_sqrt (show (25 - 4 * y : ℝ) ≥ 0 by linarith)]
        have h1 : abs (((-3 + Real.sqrt (25 - 4 * y)) / 2 : ℝ) ^ 2 - 4) = 4 - ((-3 + Real.sqrt (25 - 4 * y)) / 2) ^ 2 := by
          have h24 : ((-3 + Real.sqrt (25 - 4 * y)) / 2 : ℝ) ^ 2 - 4 ≤ (0 : ℝ) := by
            nlinarith [Real.sqrt_nonneg (25 - 4 * y), Real.sq_sqrt (show (25 - 4 * y : ℝ) ≥ 0 by linarith)]
          rw [abs_of_nonpos (by linarith)]
          all_goals linarith
        rw [h1]
        nlinarith [Real.sqrt_nonneg (25 - 4 * y), Real.sq_sqrt (show (25 - 4 * y : ℝ) ≥ 0 by linarith)]
    · -- This case is impossible, since y ≤ 25/4 by assumption. Corrected from original by using assumption
      linarith