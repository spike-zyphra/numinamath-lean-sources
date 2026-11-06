import Mathlib

theorem algebra_175250 {f : ℤ → ℝ} (h : ∀ x y, f (x - y ^ 2) = f x + (y ^ 2 - 2 * x) * f y) :
    ∃ a : ℝ, f 1984 = a * 1984^2 := by 
  use f 1984 / (1984 : ℝ) ^ 2
  have eq2 : f 0 = 0 := by
    have eq2 := h 1 0
    norm_num at eq2
    linarith

  have eq3 : ∀ y : ℤ, f (y ^ 2) = (y ^ 2 : ℝ) * f y := by
    intro y 
    have eq4 := h (y ^ 2) y 
    simp [eq2] at eq4 ⊢ 
    linarith

  have h1 := h 1984 44
  have h2 := h 1984 45
  have h3 := h 1984 1
  have h4 := h 1984 0

  norm_num [eq2] at h1 h2 h3 h4
  field_simp at *
  <;> norm_num [eq2] at h1 h2 h3 h4 eq3
  <;> linarith