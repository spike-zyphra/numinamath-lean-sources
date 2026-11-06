import Mathlib

theorem algebra_291385 {A B : ℕ} (h₀ : A + B = 1149) (h₁ : A / B = 8) (h₂ : A % B = 24) :
    A = 1024 := by 
  have h3 : B ≠ 0 := by 
    by_contra h
    rw [h] at h₁
    norm_num at h₁ 
  have h4 : A = B * 8 + 24 := by 
    rw [←Nat.div_add_mod A B, h₁, h₂]
    all_goals omega 
  omega