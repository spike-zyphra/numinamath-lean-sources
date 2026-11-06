import Mathlib

open Real Set
open scoped Real

theorem inequalities_226051 (α β : ℝ) (hα : α ∈ Ioo 0 (π/2)) (hβ : β ∈ Ioo 0 (π/2)) :
    cos α + cos β + sqrt 2 * sin α * sin β ≤ 3 * sqrt 2 / 2 := by
  rcases hα with ⟨h1, h2⟩
  rcases hβ with ⟨h3, h4⟩
  have h5 : cos α ^ 2 + sin α ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq α
  have h6 : cos β ^ 2 + sin β ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq β
  have h7 : 0 < cos α := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith
  have h8 : 0 < cos β := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith
  have h9 : 0 < sin α := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h10 : 0 < sin β := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  nlinarith [sq_nonneg (cos α - Real.sqrt 2 / 2), sq_nonneg (cos β - Real.sqrt 2 / 2),
          sq_nonneg (sin α - sin β), sq_nonneg (cos α - cos β),
          Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
          mul_nonneg (show 0 ≤ Real.sqrt 2 by positivity) (show 0 ≤ Real.sqrt 2 by positivity),
          sq_nonneg (cos α * cos β - 1 / 2),
          sq_nonneg (sin α * sin β - 1 / 2),
          mul_pos h7 h8, mul_pos h9 h10
  ]