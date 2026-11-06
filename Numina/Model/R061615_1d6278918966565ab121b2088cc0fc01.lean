import Mathlib

theorem number_theory_321637 (n : ℕ) : ¬ 7 ∣ (4^n + 1) := by 
  have h1 : ∀ (n : ℕ), 4^n % 7 = 4 ∨ 4^n % 7 = 2 ∨ 4^n % 7 = 1 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      have : 4 ^ (n + 1) % 7 = (4 ^ n * 4) % 7 := by ring
      rw [this]
      rcases ih with (ih | ih | ih)
      · 
        simp [Nat.mul_mod, ih]
      · 
        simp [Nat.mul_mod, ih]
      · 
        simp [Nat.mul_mod, ih]
  intro h
  have h2 : (4 ^ n + 1) % 7 = 0 := by 
    omega 
  have h3 : 4^n % 7 = 4 ∨ 4^n % 7 = 2 ∨ 4^n % 7 = 1 := h1 n
  rcases h3 with (h3 | h3 | h3)
  · 
    omega 
  · 
    omega 
  · 
    omega