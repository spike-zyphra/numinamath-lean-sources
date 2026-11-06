import Mathlib

theorem algebra_5759 : IsLeast {n | n > 0 ∧ n = round (Real.sqrt (∑ i ∈ Finset.range 505, (4 * i + 3)))} 715 := by
  constructor
  · -- Show 715 is in the set
    constructor
    · norm_num
    · -- Show 715 equals the rounded value
      have h1 : (∑ i in Finset.range 505, (4 * i + 3 : ℝ)) = (510555 : ℝ) := by
        norm_num [Finset.sum_range_succ]
      have h4 : round (Real.sqrt (∑ i in Finset.range 505, (4 * i + 3 : ℝ))) = (715 : ℤ) := by 
        rw [h1]
        have h5 : Real.sqrt (510555 : ℝ) ≥ (714.5 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (510555 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (510555 : ℝ) by norm_num)]
        have h8 : Real.sqrt (510555 : ℝ) < (715.5 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (510555 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (510555 : ℝ) by norm_num)]
        rw [round_eq]
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> (try nlinarith)
      rw [h4]
      all_goals try norm_num
  · -- Show that 715 is the least such
    intro n hn 
    rcases hn with ⟨hn_pos, hn_eq⟩
    by_contra h 
    push_neg at h
    have h1 : n < (715 : ℤ) := by linarith
    have h5 : round (Real.sqrt (∑ i in Finset.range 505, (4 * i + 3 : ℝ))) = (715 : ℤ) := by 
      have h1 : (∑ i in Finset.range 505, (4 * i + 3 : ℝ)) = (510555 : ℝ) := by
        norm_num [Finset.sum_range_succ]
      rw [h1] 
      have h5 : Real.sqrt (510555 : ℝ) ≥ (714.5 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (510555 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (510555 : ℝ) by norm_num)]
      have h8 : Real.sqrt (510555 : ℝ) < (715.5 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (510555 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (510555 : ℝ) by norm_num)]
      rw [round_eq]
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> (try nlinarith)
    have h9 : (n : ℤ) = (715 : ℤ) := by
      linarith [hn_eq, h5]
    omega