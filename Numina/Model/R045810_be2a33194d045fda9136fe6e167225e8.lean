import Mathlib

theorem number_theory_146819 (x y z : ℕ) (h : x^2 + y^2 = z^2) : 5 ∣ x ∨ 5 ∣ y ∨ 5 ∣ z := by
  by_contra h1
  push_neg at h1
  have h2 : ¬ (5 ∣ x) := h1.1
  have h3 : ¬ (5 ∣ y) := h1.2.1
  have h4 : ¬ (5 ∣ z) := h1.2.2
  have h5 : x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by 
    omega
  have h6 : y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by 
    omega
  have h7 : z % 5 = 1 ∨ z % 5 = 2 ∨ z % 5 = 3 ∨ z % 5 = 4 := by 
    omega
  have h8 : x^2 % 5 = 1 ∨ x^2 % 5 = 4 := by
    rcases h5 with (h | h | h | h)
    <;> simp [Nat.pow_mod, h]
  have h9 : y^2 % 5 = 1 ∨ y^2 % 5 = 4 := by 
    rcases h6 with (h | h | h | h)
    <;> simp [Nat.pow_mod, h]
  have h10 : z^2 % 5 = 1 ∨ z^2 % 5 = 4 := by 
    rcases h7 with (h | h | h | h)
    <;> simp [Nat.pow_mod, h]
  have h11 : (x^2 + y^2) % 5 = z^2 % 5 := by
    omega
  omega