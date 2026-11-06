import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_241501 :
  IsGreatest {√(cos (4 * x) + 7) + √(cos (4 * y) + 7) + √(cos (4 * x) + cos (4 * y) - 8 * sin x ^ 2 * sin y ^ 2 + 6) | (x : ℝ) (y : ℝ)} (6 * √2) := by
  constructor
  · -- Show that 6 * √2 is achievable by choosing x = 0, y = 0
    use 0, 0
    have h1 : cos (4 * (0 : ℝ)) = 1 := by
      simp
    have h2 : sin (0 : ℝ) = 0 := by
      simp
    have h3 : cos (4 * (0 : ℝ)) + 7 = 8 := by
      rw [h1]
      all_goals norm_num
    have h4 : cos (4 * (0 : ℝ)) + cos (4 * (0 : ℝ)) - 8 * sin (0 : ℝ) ^ 2 * sin (0 : ℝ) ^ 2 + 6 = 8 := by
      rw [h1]
      rw [h2]
      all_goals norm_num
    have h6 : √(cos (4 * (0 : ℝ)) + 7) = 2 * √2 := by
      rw [show cos (4 * (0 : ℝ)) + 7 = 8 by
        rw [h1]
        all_goals norm_num
      ]
      have h7 : √8 = 2 * √2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h7]
    have h11 : √(cos (4 * (0 : ℝ)) + cos (4 * (0 : ℝ)) - 8 * sin (0 : ℝ) ^ 2 * sin (0 : ℝ) ^ 2 + 6) = 2 * √2 := by
      rw [h4]
      have h7 : √8 = 2 * √2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h7]
    linarith [h6, h11]
  · -- Show that 6 * √2 is an upper bound for all elements in the set
    intro z hz
    rcases hz with ⟨x, y, hz⟩
    have h1 : cos (4 * x) ≤ 1 := by
      apply cos_le_one
    have h2 : cos (4 * y) ≤ 1 := by
      apply cos_le_one
    have h3 : cos (4 * x) + 7 ≤ 8 := by
      nlinarith [h1]
    have h4 : cos (4 * y) + 7 ≤ 8 := by
      nlinarith [h2]
    have h5 : cos (4 * x) + cos (4 * y) - 8 * sin x ^ 2 * sin y ^ 2 + 6 ≤ 8 := by
      nlinarith [Real.cos_le_one (4 * x), Real.cos_le_one (4 * y),
        sq_nonneg (sin x), sq_nonneg (sin y), 
        sq_nonneg (cos x), sq_nonneg (cos y), 
        Real.cos_sq_add_sin_sq x, Real.cos_sq_add_sin_sq y, 
        mul_nonneg (show sin x ^ 2 ≥ 0 by positivity) (show sin y ^ 2 ≥ 0 by positivity)]
    have h6 : √(cos (4 * x) + 7) ≤ 2 * √2 := by
      have h7 : cos (4 * x) + 7 ≤ 8 := h3
      have h8 : √(cos (4 * x) + 7) ≤ √(8 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h9 : √(8 : ℝ) = 2 * √2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      linarith [h8, h9]
    have h7 : √(cos (4 * y) + 7) ≤ 2 * √2 := by
      have h8 : cos (4 * y) + 7 ≤ 8 := h4
      have h9 : √(cos (4 * y) + 7) ≤ √(8 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h10 : √(8 : ℝ) = 2 * √2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      linarith [h9, h10]
    have h8 : √(cos (4 * x) + cos (4 * y) - 8 * sin x ^ 2 * sin y ^ 2 + 6) ≤ 2 * √2 := by
      have h9 : cos (4 * x) + cos (4 * y) - 8 * sin x ^ 2 * sin y ^ 2 + 6 ≤ 8 := h5
      have h10 : √(cos (4 * x) + cos (4 * y) - 8 * sin x ^ 2 * sin y ^ 2 + 6) ≤ √(8 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h11 : √(8 : ℝ) = 2 * √2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      linarith [h10, h11]
    nlinarith [hz, h6, h7, h8, mul_nonneg (show √2 ≥ 0 by positivity) (show (0 : ℝ) ≤ 2 by norm_num)]