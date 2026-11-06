import Mathlib

theorem algebra_6701 : {(s, t, u) : ℝ×ℝ×ℝ | 7 * s + 4 * t + 2 * u = -3 ∧ 7 * s + 7 * t + 2 * u = 7 ∧ 7 * s + 4 * t + 6 * u = -2} = {(-101 / 42, 10 / 3, 1 / 4)} := by
  ext ⟨s, t, u⟩
  simp
  constructor <;> {
    rintro ⟨h₁, h₂, h₃⟩
    refine' ⟨_, _, _⟩ <;> linarith
  }
