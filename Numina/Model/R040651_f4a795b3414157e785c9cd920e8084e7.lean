import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_151875 {f : ℝ → ℝ} (hf : f = λ x => x^2 * (2 - x)) :
    MonotoneOn f (Set.Ioo 0 (4 / 3)) := by 
  intro x hx y hy hxy 
  have h1 : 0 < x := hx.1 
  have h2 : x < 4 / 3 := hx.2 
  have h3 : 0 < y := hy.1 
  have h4 : y < 4 / 3 := hy.2 
  have h5 : x ≤ y := hxy 
  have h6 : f x ≤ f y := by 
    rw [hf] 
    have h7 : (x : ℝ) ^ 2 * (2 - x) ≤ (y : ℝ) ^ 2 * (2 - y) := by 
      have h8 : 0 < x := h1 
      have h9 : x < 4 / 3 := h2 
      have h10 : 0 < y := h3 
      have h11 : y < 4 / 3 := h4 
      have h12 : x ≤ y := h5 
      have h13 : (x - y) * (2 * (x + y) - (x ^ 2 + x * y + y ^ 2)) ≤ 0 := by 
        have h14 : x - y ≤ 0 := by linarith 
        have h15 : 2 * (x + y) - (x ^ 2 + x * y + y ^ 2) ≥ 0 := by 
          nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), 
            sq_nonneg (x + y - 4 / 3), mul_pos h1 h3, mul_pos h1 (show (0) < 4 / 3 - x by linarith), 
            mul_pos h3 (show (0) < 4 / 3 - y by linarith)
          ] 
        nlinarith 
      linarith 
    simpa using h7 
  exact h6