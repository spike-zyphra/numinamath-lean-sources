import Mathlib

theorem number_theory_176895 : ¬∃ x : ℕ, x ≤ 30 ∧ (x - 1) * 1 + (x - 2) * 2 + (x - 3) * 3 + (x - 4) * 4 + (x - 5) * 5 = 64 := by
  rintro ⟨x, ⟨hx1, hx2⟩⟩
  interval_cases x <;> omega