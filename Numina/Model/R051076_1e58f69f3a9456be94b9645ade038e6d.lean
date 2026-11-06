import Mathlib

theorem algebra_602558 (a b c : ℝ) (h : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 ∧ b * x ^ 2 + c * x + a = 0 ∧ c * x ^ 2 + a * x + b = 0) :
    a + b + c = 0 := by
  rcases h with ⟨x, h1, h2, h3⟩
  have h4 : (a + b + c) * (x^2 + x + 1) = 0 := by
    nlinarith
  have h5 : x^2 + x + 1 ≠ 0 := by
    nlinarith [sq_nonneg (x + 1 / 2)]
  have h6 : (a + b + c) = 0 := by
    apply_fun (fun y => y / (x^2 + x + 1)) at h4
    field_simp [h5] at h4
    linarith
  exact h6