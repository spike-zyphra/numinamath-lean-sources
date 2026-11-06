import Mathlib

theorem algebra_15194 {a b : ℝ} (ha : a ≠ 0) (x y : ℝ) (h : x ≠ y ∧ a * x ^ 2 - 2 * a * x + b = 0 ∧ a * y ^ 2 - 2 * a * y + b = 0) :
    (x + y) / 2 = 1 := by
  rcases h with ⟨hxy, hx, hy⟩
  have h_eq : a * (x^2 - y^2) - 2 * a * (x - y) = 0 := by
    linarith
  have h_eq2 : (x - y) * (a * (x + y) - 2 * a) = 0 := by 
    have h1 : a * (x^2 - y^2) - 2 * a * (x - y) = (x - y) * (a * (x + y) - 2 * a) := by 
      ring 
    rw [h1] at h_eq 
    linarith 
  cases (mul_eq_zero.mp h_eq2) with 
  | inl h1 => 
    exfalso 
    have h2 : x = y := by linarith 
    contradiction 
  | inr h2 => 
    have h3 : a * (x + y - 2) = 0 := by 
      linarith 
    have h4 : x + y - 2 = 0 := by 
      apply (mul_eq_zero.1 h3).resolve_left 
      exact ha 
    linarith