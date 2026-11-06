import Mathlib

def f (x y : ℝ) := x + y

def g (x y : ℝ) := x * y

theorem algebra_242818 {g : ℝ → ℝ → ℝ} (h₀ : ∀ x, g x x = x) (h₁ : ∀ x, g x 0 = 2 * x)
    (h₂ : ∀ x y z w, f (g x y) (g z w) = f (g x z) (g y w)) :
    g (f 2 3) (f 0 3) = 7 ∧ g 1024 48 = 49152 := by
  have h3 : g 1 0 = 2 := by
    specialize h₁ 1
    norm_num at h₁ ⊢
    linarith
  have h4 : g 1 1 = 1 := by 
    specialize h₀ 1
    all_goals linarith
  have h7 : g 0 0 = 0 := by
    specialize h₁ 0
    norm_num at h₁ ⊢
    linarith
  have h6 : f (g 1 0) (g 1 0) = f (g 1 1) (g 0 0) := by
    apply h₂ 1 0 1 0
  simp [f] at h6
  norm_num [h3, h4, h7] at h6
  all_goals nlinarith