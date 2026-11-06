import Mathlib

theorem number_theory_111073 (x y : ℕ) (hx : x > 0) (hy : y > 0)
    (h : x^2 - 2 * Nat.factorial y = 2021) :
    (x, y) = (45, 2) := by
  have h1 : x^2 = 2021 + 2 * Nat.factorial y := by
    have h2 : x^2 = 2021 + 2 * Nat.factorial y := by
      omega
    omega
  by_cases h2 : y ≤ 7
  · -- If y ≤ 7, then we can do exhaustive search
    interval_cases y <;> try { 
      norm_num [Nat.factorial] at h1 
      have h3 : x ≤ 300 := by
        nlinarith
      interval_cases x <;> norm_num at h1 <;> tauto
    }
  · -- Now consider the case where y > 7, need to show contradiction.
    have h3 : y ≥ 8 := by 
      omega
    have h4 : y ≥ 8 := h3
    have h5 : 3 ∣ Nat.factorial y := by
      apply Nat.dvd_factorial
      all_goals 
        omega
    have h6 : (x : ℕ) ^ 2 % 3 = 0 ∨ (x : ℕ) ^ 2 % 3 = 1 := by
      have h1 : (x : ℕ) % 3 = 0 ∨ (x : ℕ) % 3 = 1 ∨ (x : ℕ) % 3 = 2 := by
        omega
      rcases h1 with (h1 | h1 | h1)
      · -- x ≡ 0 (mod 3)
        simp [pow_two, Nat.mul_mod, h1]
      · -- x ≡ 1 (mod 3)
        simp [pow_two, Nat.mul_mod, h1]
      · -- x ≡ 2 (mod 3)
        simp [pow_two, Nat.mul_mod, h1]
    have h7 : 2 * Nat.factorial y % 3 = 0 := by
      have h8 : 3 ∣ Nat.factorial y := h5
      obtain ⟨k, hk⟩ := h8
      omega
    have h8 : x ^ 2 % 3 = 2 := by
      have h11 : x ^ 2 = 2021 + 2 * Nat.factorial y := h1
      have h13 : Nat.factorial y % 3 = 0 := by
        omega
      omega
    omega