import Mathlib

/-If tan x+tan y=25 and cotx+coty=30, what is tan(x+y)?-/
theorem algebra_16647 {x y : ℝ}  (h₀ : Real.tan x + Real.tan y = 25) (h₁ : 1 / Real.tan x + 1 / Real.tan y = 30) :
Real.tan (x + y) = 150 := by
--We first prove that the den.s of h₁ are all nonzero.
  have hx:Real.tan x≠0:=by
    contrapose! h₁
    rw[h₁]
    norm_num
    rw[h₁,zero_add] at h₀
    rw[h₀]
    norm_num
  have hy:Real.tan y≠0:=by
    contrapose! h₁
    rw[h₁]
    norm_num
    rw[h₁,add_zero] at h₀
    rw[h₀]
    norm_num
--We simplify h₁ and then solve the equation.
  field_simp at h₁
  rw[add_comm,h₀] at h₁
  rw[Real.tan_add',h₀]
  rw[div_eq_iff]
  linarith
  linarith
--Now we prove that all terms are well-defined.
  rw[←Real.cos_ne_zero_iff,←Real.cos_ne_zero_iff]
  constructor
  · by_contra! h
    rw[Real.tan_eq_sin_div_cos] at hx
    rw[h,div_zero] at hx
    simp only [ne_eq, not_true_eq_false] at *
  · by_contra! h
    rw[Real.tan_eq_sin_div_cos] at hy
    rw[h,div_zero] at hy
    simp only [ne_eq, not_true_eq_false] at *