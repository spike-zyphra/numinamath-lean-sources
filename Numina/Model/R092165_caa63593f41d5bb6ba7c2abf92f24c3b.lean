import Mathlib

theorem algebra_216670 {V : ℝ} {α : ℝ} {hα : 0 < α ∧ α < 1} (hV : V > 0)
    (h : α * (1 - α) * V + 0.5 * α ^ 2 * V = α * V) :
    α = 0.5 ∧ V = 24 ∧ I = 7 → (1 - α) * V + 0.5 * α ^ 2 * V = 10 := by 
  intro h1
  rcases h1 with ⟨ha1, ha2, ha3⟩
  rw [ha1, ha2] at h ⊢
  norm_num at h ⊢
  all_goals linarith