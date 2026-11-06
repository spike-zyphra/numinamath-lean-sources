import Mathlib

open Real Set
open scoped Real

theorem algebra_257065 (α β ω : ℝ) (h : α + β = ω) :
  cos α ^ 2 + cos β ^ 2 - 2 * cos α * cos β * cos ω = sin ω ^ 2 := by
  have h1 : ω = α + β := by linarith
  rw [show ω = α + β by linarith]
  have h_cos : cos (α + β) = cos α * cos β - sin α * sin β := by
    rw [cos_add]
  have h_sin : sin (α + β) = sin α * cos β + cos α * sin β := by
    rw [sin_add]
  rw [h_cos, h_sin]
  have h2 : sin α ^ 2 + cos α ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq α
  have h3 : sin β ^ 2 + cos β ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq β
  nlinarith [sq_nonneg (cos α - cos β), sq_nonneg (sin α - sin β), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, sq_nonneg (cos α * sin β - cos β * sin α), sq_nonneg (cos α - cos β), sq_nonneg (sin α - sin β)]