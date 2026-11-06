import Mathlib

theorem number_theory_604122 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ IsSquare (400 * 10000 + n)} = {4001, 8004} := by
  ext n
  simp at *
  constructor <;> intro h
  · rcases h with ⟨h₀, h⟩
    rcases h with ⟨r, hr⟩; rcases h₀ with ⟨h₀₁, h₀₂⟩
    have h₁ : 2000 ≤ r := by nlinarith
    have h₂ : r ≤ 2004 := by nlinarith
    interval_cases r <;> omega
  · rcases h with (rfl | rfl)
    · native_decide
    · native_decide
