import Mathlib

theorem number_theory_118523 : (Nat.Prime 1163) ∧ ¬(Nat.Prime 16424) := by
  have h1 : Nat.Prime 1163 := by
    norm_num
  have h2 : ¬Nat.Prime 16424 := by
    norm_num
  exact ⟨h1, h2⟩