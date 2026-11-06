import Mathlib.Tactic

theorem number_theory_126965 (d : ℤ) (hd : d > 0) (hne2 : d ≠ 2) (hne5 : d ≠ 5) (hne13 : d ≠ 13) :
    ∃ a b : ℤ, (a = 2 ∧ b = 5) ∨ (a = 2 ∧ b = 13) ∨ (a = 5 ∧ b = 13) ∨ (a = d ∧ b = 2) ∨
    (a = d ∧ b = 5) ∨ (a = d ∧ b = 13) ∧ ¬ ∃ m : ℤ, m^2 = a * b - 1 := by
  refine' ⟨2, 5, Or.inl ⟨rfl, rfl⟩⟩