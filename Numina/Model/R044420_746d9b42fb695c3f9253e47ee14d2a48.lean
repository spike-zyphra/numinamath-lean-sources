import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_14725 :
  IsLeast {y : ℝ | ∃ x, y = sin x ^ 4 + 3 / 2 * cos x ^ 4} (3 / 5) := by
  constructor
  · -- Show 3/5 is in the set
    use (Real.arcsin (Real.sqrt (3 / 5)))
    have h1 : sin (Real.arcsin (Real.sqrt (3 / 5))) = Real.sqrt (3 / 5) := by
      apply Real.sin_arcsin
      · -- Show that sqrt(3/5) ≥ -1
        have h1 : Real.sqrt (3 / 5) ≥ 0 := Real.sqrt_nonneg (3 / 5)
        linarith
      · -- Show that sqrt(3/5) ≤ 1
        have h2 : Real.sqrt (3 / 5) ≤ 1 := by
          rw [Real.sqrt_le_left]
          all_goals norm_num
        linarith
    have h2 : cos (Real.arcsin (Real.sqrt (3 / 5))) = Real.sqrt (2 / 5) := by
      have hcos : cos (Real.arcsin (Real.sqrt (3 / 5))) = Real.sqrt (1 - (Real.sqrt (3 / 5)) ^ 2) := by
        rw [cos_arcsin]
      rw [hcos]
      have h3 : (Real.sqrt (3 / 5) : ℝ) ^ 2 = 3 / 5 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      rw [h3]
      have h4 : (1 - (3 / 5 : ℝ) ) = 2 / 5 := by norm_num
      rw [h4]
    rw [h1, h2]
    have h5 : (Real.sqrt (3 / 5) : ℝ) ^ 2 = 3 / 5 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    have h6 : (Real.sqrt (2 / 5) : ℝ) ^ 2 = 2 / 5 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    have h54 : (Real.sqrt (3 / 5) : ℝ) ^ 4 = ((Real.sqrt (3 / 5) : ℝ) ^ 2) ^ 2 := by ring
    have h64 : (Real.sqrt (2 / 5) : ℝ) ^ 4 = ((Real.sqrt (2 / 5) : ℝ) ^ 2) ^ 2 := by ring
    rw [h54, h64]
    rw [show ((Real.sqrt (3 / 5) : ℝ) ^ 2) ^ 2 = (3 / 5) ^ 2 by rw [h5], show ((Real.sqrt (2 / 5) : ℝ) ^ 2) ^ 2 = (2 / 5) ^ 2 by rw [h6]]
    norm_num
  · -- Show there is no smaller element in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hx]
    have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (sin x ^ 2 - 3 / 5), sq_nonneg (cos x ^ 2 - 2 / 5), sq_nonneg (sin x ^ 2 - 3 / 5), sq_nonneg (cos x ^ 2 - 2 / 5), sq_nonneg (sin x ^ 2 + cos x ^ 2 - 1), sq_nonneg (sin x), sq_nonneg (cos x)]