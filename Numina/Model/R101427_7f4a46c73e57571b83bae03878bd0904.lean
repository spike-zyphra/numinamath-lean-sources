import Mathlib

theorem algebra_124545 (α β : ℝ) (h : Real.sin α + Real.sin β = 1) :
    Real.cos α + Real.cos β ∈ Set.Icc (-Real.sqrt 3) (Real.sqrt 3) := by
  have h4 : -Real.sqrt 3 ≤ Real.cos α + Real.cos β := by
    have h5 : (Real.cos α + Real.cos β) ^ 2 ≤ 3 := by
      nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, 
            sq_nonneg (Real.sin α - Real.sin β), 
            sq_nonneg (Real.cos α - Real.cos β),
            sq_nonneg (Real.sin α - 1 / 2), 
            sq_nonneg (Real.sin β - 1 / 2),
            sq_nonneg (Real.cos α - Real.cos β),
            Real.pi_gt_three,
            Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num),
            Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
            Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]
    have h6 : -Real.sqrt 3 ≤ Real.cos α + Real.cos β := by
      have h7 : (Real.cos α + Real.cos β) ^ 2 ≤ 3 := h5
      have h8 : -Real.sqrt 3 ≤ Real.cos α + Real.cos β := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      linarith
    linarith
  have h5 : Real.cos α + Real.cos β ≤ Real.sqrt 3 := by
    have h6 : (Real.cos α + Real.cos β) ^ 2 ≤ 3 := by
      nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, 
            sq_nonneg (Real.sin α - Real.sin β), 
            sq_nonneg (Real.cos α - Real.cos β),
            sq_nonneg (Real.sin α - 1 / 2), 
            sq_nonneg (Real.sin β - 1 / 2),
            sq_nonneg (Real.cos α - Real.cos β),
            Real.pi_gt_three,
            Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num),
            Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
            Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]
    have h7 : Real.cos α + Real.cos β ≤ Real.sqrt 3 := by
      have h8 : (Real.cos α + Real.cos β) ^ 2 ≤ 3 := h6
      have h9 : Real.cos α + Real.cos β ≤ Real.sqrt 3 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      linarith
    linarith
  rw [Set.mem_Icc]
  constructor <;> linarith