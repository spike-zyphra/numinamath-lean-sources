import Mathlib

theorem number_theory_146819 (x y z : ℕ) (h : x^2 + y^2 = z^2) : 5 ∣ x ∨ 5 ∣ y ∨ 5 ∣ z := by 
  by_contra!
  have h1 : x^2 % 5 = 1 ∨ x^2 % 5 = 4 := by
    have h1 : x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1) <;>
      simp [Nat.pow_mod, h1]
  have h2 : y^2 % 5 = 1 ∨ y^2 % 5 = 4 := by
    have h2 : y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2) <;>
      simp [Nat.pow_mod, h2]
  have h3 : z^2 % 5 = 1 ∨ z^2 % 5 = 4 := by
    have h3 : z % 5 = 1 ∨ z % 5 = 2 ∨ z % 5 = 3 ∨ z % 5 = 4 := by
      omega
    rcases h3 with (h3 | h3 | h3 | h3) <;>
      simp [Nat.pow_mod, h3]
  have h4 : (x^2 + y^2) % 5 = 2 ∨ (x^2 + y^2) % 5 = 3 ∨ (x^2 + y^2) % 5 = 0 := by
    rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;>
      omega
  have h5 : (x^2 + y^2) % 5 = z^2 % 5 := by
    rw [h]
  rw [h5] at h4
  rcases h3 with (h3 | h3) <;> omega