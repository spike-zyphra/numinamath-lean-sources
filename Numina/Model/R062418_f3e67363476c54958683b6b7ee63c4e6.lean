import Mathlib

theorem algebra_225820 {a b c A B C : ℝ} (ha : a ≠ 0) (hA : A ≠ 0)
    (h : ∃ x, a * x ^ 2 + b * x + c = 0 ∧ A * x ^ 2 + B * x + C = 0) :
    (a * C - A * c) ^ 2 = (a * B - A * b) * (b * C - B * c) := by 
  rcases h with ⟨x, hx₁, hx₂⟩
  have hc : c = -a * x ^ 2 - b * x := by linarith
  have hC : C = -A * x ^ 2 - B * x := by linarith
  rw [hc, hC] 
  ring