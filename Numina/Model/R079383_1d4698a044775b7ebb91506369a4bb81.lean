import Mathlib

theorem number_theory_7856 (a b c : ℤ) :
    ∃ m : ℤ, (a + b) / 2 = m ∨ (b + c) / 2 = m ∨ (c + a) / 2 = m := by
  refine' ⟨(a + b) / 2, Or.inl rfl⟩