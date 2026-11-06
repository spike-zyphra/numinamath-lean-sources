import Mathlib

theorem number_theory_114919 (a : ℤ) : ∃ x y, x^2 - y^2 = a^5 := by 
  use (a^2 * (a + 1) ) / 2, (a^2 * (a - 1) ) / 2
  have h1 : 2 ∣ a ^ 2 * (a + 1) := by
    have h2 : a % 2 = 0 ∨ a % 2 = 1 := by
      omega
    rcases h2 with (h2 | h2)
    · -- a is even
      have h3 : a % 2 = 0 := h2
      have h4 : a ^ 2 % 2 = 0 := by
        simp [Int.add_emod, Int.mul_emod, h3, pow_two]
        <;> omega
      have h5 : (a ^ 2 * (a + 1) ) % 2 = 0 := by
        simp [Int.add_emod, Int.mul_emod, h4]
        all_goals omega
      omega
    · -- a is odd
      have h3 : a % 2 = 1 := h2
      have h4 : (a + 1) % 2 = 0 := by 
        omega
      have h5 : 2 ∣ a + 1 := by 
        omega
      have h7 : 2 ∣ a ^ 2 * (a + 1) := by 
        apply dvd_trans (show (2 : ℤ) ∣ a + 1 by omega) (show (a + 1 : ℤ) ∣ a ^ 2 * (a + 1) by
          use a^2
          all_goals 
            ring
        )
      assumption
  have h2 : 2 ∣ a ^ 2 * (a - 1) := by
    have h2 : a % 2 = 0 ∨ a % 2 = 1 := by
      omega
    rcases h2 with (h2 | h2)
    · -- a is even
      have h3 : a % 2 = 0 := h2
      have h4 : a ^ 2 % 2 = 0 := by
        simp [Int.add_emod, Int.mul_emod, h3, pow_two]
        <;> omega
      have h5 : (a ^ 2 * (a - 1) ) % 2 = 0 := by
        simp [Int.add_emod, Int.mul_emod, h4]
        all_goals omega
      omega
    · -- a is odd
      have h3 : a % 2 = 1 := h2
      have h4 : (a - 1) % 2 = 0 := by 
        omega
      have h5 : 2 ∣ a - 1 := by 
        omega
      have h7 : 2 ∣ a ^ 2 * (a - 1) := by 
        apply dvd_trans (show (2 : ℤ) ∣ a - 1 by omega) (show (a - 1 : ℤ) ∣ a ^ 2 * (a - 1) by
          use a^2
          all_goals 
            ring
        )
      assumption
  have h6 : 2 * ((a^2 * (a + 1) ) / 2 : ℤ) = a ^ 2 * (a + 1) := by 
    omega
  have h7 : 2 * ((a^2 * (a - 1) ) / 2 : ℤ) = a^2 * (a - 1) := by 
    omega
  have h5 : ((a^2 * (a + 1) ) / 2 : ℤ) ^ 2 - ((a^2 * (a - 1) ) / 2 : ℤ) ^ 2 = a ^ 5 := by
    have h8 : (2 * ((a^2 * (a + 1) ) / 2 : ℤ) ) ^ 2 - (2 * ((a^2 * (a - 1) ) / 2 : ℤ) ) ^ 2 = 4 * a ^ 5 := by
      rw [show 2 * ((a^2 * (a + 1) ) / 2 : ℤ) = a^2 * (a + 1) by omega, 
          show 2 * ((a^2 * (a - 1) ) / 2 : ℤ) = a^2 * (a - 1) by omega]
      nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a + 1), sq_nonneg (a - 1), sq_nonneg (a), sq_nonneg (a * (a + 1)), sq_nonneg (a * (a - 1)), h1, h2]
    nlinarith [sq_nonneg ((a^2 * (a + 1) ) / 2 : ℤ), sq_nonneg ((a^2 * (a - 1) ) / 2 : ℤ), sq_nonneg (a * (a + 1)), sq_nonneg (a * (a - 1)), sq_nonneg (a), sq_nonneg (a + 1), sq_nonneg (a - 1)]
  exact_mod_cast h5