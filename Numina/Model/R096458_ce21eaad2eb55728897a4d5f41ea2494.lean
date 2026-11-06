import Mathlib

theorem algebra_29146 {f : ℤ → ℤ} (h : ∀ a b c, a + b + c = 0 → f a + f b + f c = a ^ 2 + b ^ 2 + c ^ 2) :
    ∃ c, ∀ x, f x = x ^ 2 + c * x := by
  have f0 : f 0 = 0 := by 
    have h1 := h 0 0 0 (by norm_num)
    norm_num at h1 
    linarith 
  have f_add : ∀ x y : ℤ, f (x + y) = f x + f y + 2 * x * y := by 
    intro x y 
    have h1 := h x y (-x - y) (by ring) 
    have h2 := h (-x) (-y) (x + y) (by ring)
    have neg_x_eq : f (-x) = 2 * x ^ 2 - f x := by 
      have h2 := h x (-x) 0 (by ring)
      simp [f0] at h2 
      linarith 
    have neg_y_eq : f (-y) = 2 * y ^ 2 - f y := by 
      have h3 := h y (-y) 0 (by ring)
      simp [f0] at h3 
      linarith 
    have eq1 : f (x + y) = f x + f y + 2 * x * y := by 
      norm_num at h1 h2 
      linarith [h1, h2, neg_x_eq, neg_y_eq] 
    exact eq1 
  use f 1 - 1 
  intro x 
  induction x using Int.induction_on with 
  | hz =>
    simp [f0] 
  | hp y hy =>
    have eq2 := f_add y 1 
    simp at eq2 
    simp [hy] at *
    linarith [eq2] 
  | hn y hy =>
    have eq2 := f_add (-y - 1) 1 
    simp at eq2 
    simp [hy] at *
    linarith [eq2, f0]