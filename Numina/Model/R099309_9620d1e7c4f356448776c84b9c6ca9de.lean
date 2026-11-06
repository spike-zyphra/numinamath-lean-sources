import Mathlib
open Real Set

theorem algebra_2380 {f : ℝ → ℝ} (hf : f = fun x => x^2 + abs x + 1) : ¬ ∃ x, f x = 0 := by 
  rintro ⟨x, hx⟩
  rw [hf] at hx
  simp at hx
  have h1 : x ^ 2 ≥ 0 := by apply sq_nonneg
  have h2 : abs x ≥ 0 := abs_nonneg x
  linarith