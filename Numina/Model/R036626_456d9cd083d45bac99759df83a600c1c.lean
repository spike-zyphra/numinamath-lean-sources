import Mathlib

theorem number_theory_225745 (a b c : ℤ) (h₀ : a^2 + b^2 = c^2) (h₁ : a.gcd b = 1) :
    (Even a ∧ Odd b) ∨ (Even b ∧ Odd a) := by
  have h2 : (a % 2 = 0 ∨ a % 2 = 1) := by
    omega
  have h3 : (b % 2 = 0 ∨ b % 2 = 1) := by
    omega
  rcases h2 with (h2 | h2)
  · -- a is even
    rcases h3 with (h3 | h3)
    · -- b is even
      exfalso
      have h4 : (2 : ℤ) ∣ a := by 
        omega
      have h5 : (2 : ℤ) ∣ b := by
        omega
      have h8 : (2 : ℤ) ∣ a.gcd b := by
        apply Int.dvd_gcd 
        · exact h4
        · exact h5
      have h9 : a.gcd b = 1 := h₁
      rw [h9] at h8
      omega
    · -- b is odd
      left
      constructor
      · -- Show that a is even
        have h10 : Even a := by
          refine' ⟨a / 2, by omega⟩
        exact h10
      · -- Show that b is odd
        have h11 : Odd b := by
          have h11 : b % 2 = 1 := by
            omega
          exact Int.odd_iff.mpr h11
        exact h11
  · -- a is odd
    rcases h3 with (h3 | h3)
    · -- b is even
      right
      constructor
      · -- Show that b is even
        have h10 : Even b := by
          refine' ⟨b / 2, by omega⟩
        exact h10
      · -- Show that a is odd
        have h11 : Odd a := by
          have h11 : a % 2 = 1 := by
            omega
          exact Int.odd_iff.mpr h11
        exact h11
    · -- b is odd
      exfalso
      have h10 : a % 2 = 1 := by 
        omega
      have h11 : b % 2 = 1 := by
        omega
      have h14 : a ^ 2 % 8 = 1 := by
        have h12 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by 
          omega
        rcases h12 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h]
      have h15 : b ^ 2 % 8 = 1 := by
        have h13 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by 
          omega
        rcases h13 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h]
      have h16 : (a ^ 2 + b ^ 2) % 8 = 2 := by
        omega
      have h17 : c ^ 2 % 8 = 2 := by
        omega
      have h18 : c ^ 2 % 8 = 0 ∨ c ^ 2 % 8 = 1 ∨ c ^ 2 % 8 = 4 := by
        have h19 : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by 
          omega
        rcases h19 with (h | h | h | h | h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h]
      omega