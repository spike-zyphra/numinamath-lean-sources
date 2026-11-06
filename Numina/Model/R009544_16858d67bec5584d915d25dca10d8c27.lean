import Mathlib

theorem algebra_10998 {f : ℝ → ℝ} (hf : ∃ b c, f = fun x => x ^ 2 + b * x + c)
  (hf0 : f 0 = 4) (hf1 : f 1 = 10) : f = fun x => x ^ 2 + 5 * x + 4 := by 
  rcases hf with ⟨b, c, h⟩
  have h₀: c = 4 := by 
    simp [h] at hf0
    exact hf0
  have h₁: b = 5 := by 
    simp [h] at hf1
    rw [h₀] at hf1
    linarith 
  rw [h]
  funext x
  simp [h₀, h₁]
  all_goals linarith