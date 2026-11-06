import Mathlib

open Real Set
open scoped Real

/- There exists a positive real number $x$ such that $ \cos (\arctan (x)) = x $. Find the value of $x^2$. -/
theorem calculus_16832 {x : ℝ} (hx : x > 0) (h : cos (arctan x) = x) :
    x^2 = (-1 + sqrt 5) / 2 := by
  have h₀ : 0 < Real.sqrt 5 := sqrt_pos.mpr (by norm_num)
  have h₁ : cos (arctan x) ^ 2 = x ^ 2 := by rw [h]
  rw [cos_arctan] at h₁
  field_simp at h₁ ⊢
  nlinarith [Real.sq_sqrt (show 0 ≤ 5 from by norm_num)]