import Mathlib

theorem algebra_6805 {f : ℝ → ℝ} (hf : ∃ a b c, f = fun x => a * x ^ 2 + b * x + c)
    (h1 : f (-1) = 3) (h2 : f 2 = 18) (h3 : f (-2) = 6) : f 1 = 9 := by
  rcases hf with ⟨a, b, c, rfl⟩ 
  simp at h1 h2 h3 ⊢
  linarith