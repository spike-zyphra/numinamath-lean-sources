import Mathlib

theorem calculus_6395 {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (h0 : f 0 = 0) (h'0 : deriv f 0 ≠ 0)
    (h : ∀ x, 2 * f x * deriv f x + 24 * x * (x + 1) = (8 * x + 2) * f x + (4 * x ^ 2 + 2 * x + 3) * deriv f x) :
    ∀ x, f x = 2 * x + 3 := by 
  have h0_eq : f 0 = 0 := h0
  have h'0_ne : deriv f 0 ≠ 0 := h'0
  -- Now apply h at x = 0
  have eq0 := h 0
  simp [h0_eq] at eq0
  have h'0_eq_zero : deriv f 0 = 0 := by 
    linarith 
  contradiction