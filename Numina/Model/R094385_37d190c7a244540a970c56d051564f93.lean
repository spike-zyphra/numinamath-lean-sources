import Mathlib

theorem number_theory_203711 (a b c : ℤ) (h₀ : a = 3) (h₁ : b = 9) (h₂ : c = 15)
    (h₃ : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ x = a + b - c ∧ y = a + c - b ∧ z = b + c - a ∧
      min (min x y) z = 2013) :
    x = 2019 ∧ y = 2025 := by
  rcases h₃ with ⟨x, y, z, h4, h5, h6, h7, h8, h9, h10⟩
  rw [h₀] at h7 h8 h9
  rw [h₁] at h7 h8 h9
  rw [h₂] at h7 h8 h9
  norm_num at h7 h8 h9
  omega