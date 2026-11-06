import Mathlib

theorem algebra_13863 (A B C D : ℝ × ℝ)
    (h₀ : A = (0, 0)) (h₁ : B = (5, 12)) (h₂ : C = (21, 12))
    (h₃ : D = (5, 0)) (h₄ : dist A B = 13) (h₅ : dist D C = 20)
    (h₆ : dist A D = 5) :
    dist A C = 24.2 := by
  subst A
  subst B
  subst C
  subst D
  norm_num [dist] at h₄ h₅ h₆ ⊢
  all_goals
    nlinarith [Real.sqrt_nonneg 585, Real.sq_sqrt (show (0 : ℝ) ≤ (585 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (24.2 : ℝ) by norm_num)]