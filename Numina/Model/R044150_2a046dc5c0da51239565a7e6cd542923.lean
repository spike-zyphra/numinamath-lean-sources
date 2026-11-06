import Mathlib

theorem number_theory_78987 :
    {(a, b, c) : ℤ × ℤ × ℤ | a + b + c = 24 ∧ a^2 + b^2 + c^2 = 210 ∧ a * b * c = 440} =
    {(11, 8, 5), (8, 11, 5), (8, 5, 11), (5, 8, 11), (11, 5, 8), (5, 11, 8)} := by
  ext ⟨a, b, c⟩
  simp
  constructor
  · -- If (a,b,c) satisfy the system of equations, then they must be six tuple.
    rintro ⟨h₁, h₂, h₃⟩
    have h4 : a * b + b * c + c * a = 183 := by
      nlinarith
    have h5 : (a = 5 ∨ a = 8 ∨ a = 11) ∧ (b = 5 ∨ b = 8 ∨ b = 11) ∧ (c = 5 ∨ c = 8 ∨ c = 11) := by
      have h5a : a = 5 ∨ a = 8 ∨ a = 11 := by
        have h6 : a^3 - 24 * a^2 + 183 * a - 440 = 0 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
            sq_nonneg (a * b * c - 440), sq_nonneg (a + b + c - 24), sq_nonneg (a^2 + b^2 + c^2 - 210)]
        have h8 : a ≤ 24 := by
          nlinarith [sq_nonneg (a - 8), sq_nonneg (a - 11), sq_nonneg (a - 5)]
        have h9 : a ≥ 5 := by
          nlinarith [sq_nonneg (a - 8), sq_nonneg (a - 11), sq_nonneg (a - 5)]
        interval_cases a <;> omega
      have h6 : b = 5 ∨ b = 8 ∨ b = 11 := by
        have h7 : b^3 - 24 * b^2 + 183 * b - 440 = 0 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
            sq_nonneg (a * b * c - 440), sq_nonneg (a + b + c - 24), sq_nonneg (a^2 + b^2 + c^2 - 210)]
        have h8 : b ≤ 24 := by
          nlinarith [sq_nonneg (b - 8), sq_nonneg (b - 11), sq_nonneg (b - 5)]
        have h9 : b ≥ 5 := by
          nlinarith [sq_nonneg (b - 8), sq_nonneg (b - 11), sq_nonneg (b - 5)]
        interval_cases b <;> omega
      have h7 : c = 5 ∨ c = 8 ∨ c = 11 := by
        have h8 : c^3 - 24 * c^2 + 183 * c - 440 = 0 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
            sq_nonneg (a * b * c - 440), sq_nonneg (a + b + c - 24), sq_nonneg (a^2 + b^2 + c^2 - 210)]
        have h9 : c ≤ 24 := by
          nlinarith [sq_nonneg (c - 8), sq_nonneg (c - 11), sq_nonneg (c - 5)]
        have h10 : c ≥ 5 := by
          nlinarith [sq_nonneg (c - 8), sq_nonneg (c - 11), sq_nonneg (c - 5)]
        interval_cases c <;> omega
      exact ⟨h5a, h6, h7⟩
    rcases h5 with ⟨ha, hb, hc⟩
    rcases ha with (rfl | rfl | rfl)
    all_goals
      rcases hb with (rfl | rfl | rfl)
      all_goals
        rcases hc with (rfl | rfl | rfl)
        all_goals
          omega
  · -- Check that the six tuple satisfy the system of equations.
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    all_goals
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num