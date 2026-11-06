import Mathlib

theorem algebra_94836 (granny_smith elberta anjou : ℕ) (h₀ : granny_smith = 63) (h₁ : elberta = anjou + 2)
    (h₂ : anjou = granny_smith / 3) : elberta = 23 := by 
  subst h₀
  norm_num at h₂ 
  subst h₂ 
  subst h₁ 
  all_goals omega