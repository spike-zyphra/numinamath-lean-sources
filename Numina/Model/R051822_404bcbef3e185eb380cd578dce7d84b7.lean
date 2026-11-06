import Mathlib

theorem number_theory_30083 (m n : ℤ) : ¬(2560*m^2 + 5*m + 6 = n^5) := by
  intro h
  have h1 : n^5 % 5 = n % 5 := by
    have h2 : n^5 % 5 = n % 5 := by
      have h3 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by 
        omega
      rcases h3 with (h3 | h3 | h3 | h3 | h3) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h3]
    exact h2
  have h2 : (2560 * m^2 + 5 * m + 6) % 5 = 1 := by
    omega
  have h3 : n % 5 = 1 := by
    omega
  have h4 : n % 25 = 1 ∨ n % 25 = 6 ∨ n % 25 = 11 ∨ n % 25 = 16 ∨ n % 25 = 21 := by
    omega
  have h5 : (n^5) % 25 = 1 := by
    rcases h4 with (h4 | h4 | h4 | h4 | h4) <;> 
      norm_num [pow_succ, Int.add_emod, Int.mul_emod, h4] at *
  have h6 : (2560 * m^2 + 5 * m + 6) % 25 = 1 := by
    omega
  have h7 : (10 * m^2 + 5 * m) % 25 = 20 := by
    omega
  have h8 : (2 * m^2 + m) % 5 = 4 % 5 := by
    omega
  have h10 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by
    omega
  rcases h10 with (h10 | h10 | h10 | h10 | h10) <;> 
    norm_num [pow_two, Int.add_emod, Int.mul_emod, h10] at h8 <;> omega