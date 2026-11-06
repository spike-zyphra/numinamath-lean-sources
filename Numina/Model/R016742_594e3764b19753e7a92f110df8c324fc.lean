import Mathlib

open Real Set
open scoped Real

theorem inequalities_138129 (α β γ : Real)
  (h : sin α + sin β + sin γ ≥ 2) :
  cos α + cos β + cos γ ≤ sqrt 5 := by
  have h2 : (cos α + cos β + cos γ) ^ 2 ≤ 5 := by
    nlinarith [sq_nonneg ((sin α + sin β + sin γ) - 2), h, sq_nonneg ((cos α + cos β + cos γ) ^ 2), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq γ, sq_nonneg (cos α - cos β), sq_nonneg (cos β - cos γ), sq_nonneg (cos γ - cos α), sq_nonneg (sin α - sin β), sq_nonneg (sin β - sin γ), sq_nonneg (sin γ - sin α)]
  have h3 : cos α + cos β + cos γ ≤ Real.sqrt 5 := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  exact h3