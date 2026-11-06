import Mathlib

theorem algebra_175872 {x y : ℤ} (h₀ : x + y = 20) (h₁ : x^2 + y^2 = 202) :
    x = 9 ∧ y = 11 ∨ x = 11 ∧ y = 9 := by
  have h2 : y = 20 - x := by linarith
  rw [h2] at h₁
  -- Now we have x^2 + (20 - x)^2 = 202
  -- Expanding this:
  -- x^2 + (400 - 40x + x^2) = 202
  -- Therefore:
  -- 2x^2 - 40x + 400 - 202 = 0
  -- 2x^2 - 40 x + 198 =0
  -- Then dividing by 2:
  -- x^2 - 20 x + 99 = 0
  -- Solving the quadratic:
  -- x = [20 ± sqrt(4)] / 2 = [20 ± 2] / 2
  -- Therefore:
  -- x can be 9 or 11
  have h5 : 2 * x^2 - 40 * x + 198 = 0 := by
    nlinarith
  -- Divide the quadratic equation by 2:
  have h6 : x^2 - 20 * x + 99 = 0 := by
    linarith
  have h7 : x = 9 ∨ x = 11 := by
    have h8 : x^2 - 20 * x + 99 = 0 := h6
    have h9 : x^2 - 20 * x + 99 = (x - 9) * (x - 11) := by ring
    rw [h9] at h8
    cases' (mul_eq_zero.1 h8) with h10 h11
    · -- x - 9 = 0
      left
      linarith
      all_goals
      try tauto
    · -- x - 11 = 0
      right
      linarith
      all_goals
      try tauto
  cases' h7 with h8 h9
  · -- x = 9
    have hx : x = 9 := h8
    have hy : y = 11 := by
      linarith [h₀, hx]
    left
    exact ⟨hx, hy⟩
  · -- x = 11
    have hx : x = 11 := h9
    have hy : y = 9 := by
      linarith [h₀, hx]
    right
    exact ⟨hx, hy⟩