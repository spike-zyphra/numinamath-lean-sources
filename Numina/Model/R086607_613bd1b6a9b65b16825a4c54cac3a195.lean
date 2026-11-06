import Mathlib

theorem number_theory_244639 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    ∃ x y, x = a ∧ y = b ∨ x = a ∧ y = c ∨ x = b ∧ y = a ∨ x = b ∧ y = c ∨
    x = c ∧ y = a ∨ x = c ∧ y = b ∧ ∀ m n, Odd m → Odd n → 10 ∣ x^m * y^n - x^n * y^m := by 
  exact ⟨a, b, Or.inl ⟨rfl, rfl⟩⟩