import Mathlib

theorem algebra_6701 : {(s, t, u) : ℝ×ℝ×ℝ | 7 * s + 4 * t + 2 * u = -3 ∧ 7 * s + 7 * t + 2 * u = 7 ∧ 7 * s + 4 * t + 6 * u = -2} = {(-101 / 42, 10 / 3, 1 / 4)} := by
  ext ⟨s, t, u⟩
  simp
  constructor
  · -- Assume (s, t, u) satisfies all three equations, prove it equals the solution
    rintro ⟨h1, h2, h3⟩
    have eq1 : t = 10 / 3 := by
      linarith
    have eq2 : u = 1 / 4 := by
      rw [eq1] at h1 h3
      linarith
    have eq3 : s = -101 / 42 := by
      rw [eq1, eq2] at h1
      linarith
    simp [eq1, eq2, eq3]
  · -- Assume (s, t, u) is the solution, prove it satisfies all three equations
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num