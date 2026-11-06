import Mathlib

theorem algebra_19973 {A B C D : ℝ × ℝ}
    (h₀ : A.1 = 0 ∧ A.2 = 4)
    (h₁ : B.1 = -3 ∧ B.2 = 0)
    (h₂ : C.1 = 6 ∧ C.2 = 0)
    (h₃ : D.1 = 0 ∧ D.2 = 0)
    (h₄ : dist D C = 2 * dist B D) :
    (1 / 2) * dist B C * dist A D = 18 := by 
  rcases h₀ with ⟨hx_A, hy_A⟩
  rcases h₁ with ⟨hx_B, hy_B⟩
  rcases h₂ with ⟨hx_C, hy_C⟩
  rcases h₃ with ⟨hx_D, hy_D⟩
  have h5 : dist B C = 9 := by 
    simp [dist_eq_norm, hx_B, hy_B, hx_C, hy_C, Prod.norm_def]
    all_goals norm_num [Real.sqrt_eq_iff_sq_eq]
  have h6 : dist A D = 4 := by
    simp [dist_eq_norm, hx_A, hy_A, hx_D, hy_D, Prod.norm_def]
    all_goals norm_num [Real.sqrt_eq_iff_sq_eq]
  rw [h5, h6]
  all_goals norm_num