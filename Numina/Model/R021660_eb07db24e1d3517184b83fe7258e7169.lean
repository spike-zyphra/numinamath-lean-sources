import Mathlib

theorem algebra_2466 {a b c : ℝ} (ha : a ≠ 0) (x₁ x₂ : ℝ)
    (hroots : a * x₁ ^ 2 + b * x₁ + c = 0 ∧ a * x₂ ^ 2 + b * x₂ + c = 0) :
    a * (x₁ ^ 1993 + 1993 * x₂ ^ 1993) +
    b * (x₁ ^ 1992 + 1993 * x₂ ^ 1992) +
    c * (x₁ ^ 1991 + 1993 * x₂ ^ 1991) = 0 := by
  rcases hroots with ⟨h₁, h₂⟩
  have eq₁ : a * (x₁ ^ 1993 + 1993 * x₂ ^ 1993) + b * (x₁ ^ 1992 + 1993 * x₂ ^ 1992) + c * (x₁ ^ 1991 + 1993 * x₂ ^ 1991) =
          x₁ ^ 1991 * (a * x₁ ^ 2 + b * x₁ + c) + 1993 * x₂ ^ 1991 * (a * x₂ ^ 2 + b * x₂ + c) := by
    ring
  rw [eq₁]
  rw [h₁, h₂]
  all_goals norm_num