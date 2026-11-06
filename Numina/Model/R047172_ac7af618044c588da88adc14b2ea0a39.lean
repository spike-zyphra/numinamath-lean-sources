import Mathlib


theorem number_theory_194215 (n : ℕ) (h : Odd n) :
    48 ∣ n^3 + 3 * n^2 - n - 3 := by
  have h1 : n % 2 = 1 := by
    obtain ⟨k, hk⟩ := h
    omega

  have h2 : (n ^ 3 + 3 * n ^ 2 - n - 3) % 3 = 0 := by
    have h31 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h31 with (h31 | h31 | h31)
    ·
      simp [Nat.add_mod, Nat.mul_mod, pow_two, pow_succ, Nat.sub_mod_eq_zero_of_mod_eq, h31]
    ·
      simp [Nat.add_mod, Nat.mul_mod, pow_two, pow_succ, Nat.sub_mod_eq_zero_of_mod_eq, h31]
    ·
      simp [Nat.add_mod, Nat.mul_mod, pow_two, pow_succ, Nat.sub_mod_eq_zero_of_mod_eq, h31]

  have h4 : (n ^ 3 + 3 * n ^ 2 - n - 3) % 16 = 0 := by
    obtain ⟨k, hk⟩ := h
    have eq1 : n = 2 * k + 1 := by
      omega
    rw [eq1]
    have eq2 : (2 * k + 1 : ℕ) ^ 3 + 3 * (2 * k + 1 : ℕ) ^ 2 - (2 * k + 1 : ℕ) - 3 = 8 * k ^ 3 + 24 * k ^ 2 + 16 * k := by
      cases k with
      | zero =>
        all_goals omega
      | succ k =>
        simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.pow_zero, Nat.mul_assoc]
        ring_nf
        <;> omega

    rw [eq2]
    have eq3 : (8 * k ^ 3 + 24 * k ^ 2 + 16 * k) % 16 = 0 := by
      have eq4 : 8 * k ^ 3 + 24 * k ^ 2 + 16 * k = 8 * (k * (k + 1) * (k + 2)) := by
        ring
      rw [eq4]
      have h71 : (k * (k + 1) * (k + 2)) % 2 = 0 := by
        have h711 : k % 2 = 0 ∨ k % 2 = 1 := by
          omega
        rcases h711 with (h711 | h711)
        ·
          simp [Nat.mul_mod, Nat.add_mod, h711]
        ·
          simp [Nat.mul_mod, Nat.add_mod, h711]
      have eq5 : (8 * (k * (k + 1) * (k + 2))) % 16 = 0 := by
        omega
      omega
    omega

  omega