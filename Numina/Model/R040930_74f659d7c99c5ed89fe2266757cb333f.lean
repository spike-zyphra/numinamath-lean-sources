import Mathlib

theorem algebra_263600 {f : ℝ → ℝ} (h : ∀ x y, y * f (2 * x) - x * f (2 * y) = 8 * x * y * (x ^ 2 - y ^ 2)) :
    ∃ c, ∀ x, f x = x ^ 3 + c * x := by 
  have h1 : f 0 = 0 := by 
    specialize h 0 1
    norm_num at h
    linarith
  have h2 : ∀ x : ℝ, f (2 * x) - x * f 2 = 8 * x * (x ^ 2 - 1) := by
    intro x
    specialize h x 1
    norm_num at h 
    linarith
  use (f 2 / 2 - 4)
  intro x
  have eq1 := h2 (x / 2)
  have eq2 : f (2 * (x / 2)) = f x := by 
    ring_nf 
  rw [eq2] at eq1 
  have eq3 : f x = x ^ 3 + (f 2 / 2 - 4) * x := by
    field_simp at eq1 ⊢ 
    ring_nf at eq1 ⊢
    linarith 
  exact eq3