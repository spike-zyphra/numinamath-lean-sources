import Mathlib

theorem number_theory_234125 :
    IsGreatest {x : ℚ | ∃ a b c : ℕ, x = 77 / 780 ∧ a * 195 = b * 156 ∧ b * 130 = c * 154} (77 / 780) := by
  constructor
  · -- Show that 77/780 is in the set.
    use 308, 385, 325
    all_goals norm_num
  · -- Show that 77/780 is greatest.
    intro x hx
    rcases hx with ⟨a, b, c, hx_eq, h1, h2⟩
    have h3 : (x : ℚ) = (77 / 780 : ℚ) := by
      simpa using hx_eq
    rw [h3]
    all_goals norm_num