import Mathlib

theorem algebra_272012 {b c : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + b * x + c)
    (h : ¬∃ x : ℝ, f x = x) : ¬∃ x : ℝ, f (f x) = x := by
  intro h1 
  rcases h1 with ⟨x, hx⟩ 
  have h3 : f (f x) = x := hx
  have eq1 : f x = x ^ 2 + b * x + c := hf x
  have eq2 : f (f x) = (f x) ^ 2 + b * (f x) + c := hf (f x)
  rw [eq2] at h3 
  have eq4 : f x = x ^ 2 + b * x + c := eq1
  have eq5 : (f x) ^ 2 + b * (f x) + c = x := by linarith 
  have h7 : (f x - x) * (f x + x + b + 1) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.1 h7) with h_eq1 h_eq2
  · -- Case f x - x = 0, i.e. f x = x 
    exfalso 
    have h_eq5 : ∃ x, f x = x := by 
      refine' ⟨x, by linarith⟩ 
    contradiction 
  · -- h_eq2 is f x + x + b + 1 = 0 
    have h_eq8 : f x + x + b + 1 = 0 := h_eq2 
    have h_eq9 : (b - 1) ^ 2 - 4 * c ≥ 0 := by 
      have eq6 : x ^ 2 + (b + 1) * x + (c + b + 1) = 0 := by 
        have eq6' : f x = -x - b - 1 := by 
          linarith 
        rw [eq6'] at eq4 
        nlinarith 
      nlinarith [sq_nonneg (x + (b + 1) / 2), sq_nonneg (x + (b - 1) / 2)]
    have h_eq5 : ∃ y, f y = y := by 
      use ((1 - b) - Real.sqrt ((b - 1) ^ 2 - 4 * c)) / 2 
      rw [hf]
      nlinarith [Real.sqrt_nonneg ((b - 1) ^ 2 - 4 * c), Real.sq_sqrt (show (b - 1) ^ 2 - 4 * c ≥ 0 by linarith)]
    contradiction