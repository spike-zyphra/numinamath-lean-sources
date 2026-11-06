import Mathlib

theorem number_theory_115181 (n : ℤ) : ¬(121 ∣ n^2 + 2 * n + 12) := by 
  intro h
  -- 11 ∣ n + 1
  have h1 : n % 11 = 10 := by 
    have h2 : (n ^ 2 + 2 * n + 12) % 121 = 0 := by 
      omega
    have h3 : (n ^ 2 + 2 * n + 12) % 11 = 0 := by 
      omega
    have h4 : n % 11 = 10 := by 
      have : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by 
        omega
      rcases this with (h | h | h | h | h | h | h | h | h | h | h) <;> ( 
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod] at h3
        <;> omega
      )
    assumption
  -- if 11 ∣ n + 1 then 11 ^ 2 ∣ (n+ 1) ^ 2
  have h5 : (n ^ 2 + 2 * n + 12) % 121 ≠ 0 := by 
    have h6 : n % 11 = 10 := h1
    have h7 : n % 121 = 10 ∨ n % 121 = 21 ∨ n % 121 = 32 ∨ n % 121 = 43 ∨ n % 121 = 54 ∨ n % 121 = 65 ∨ n % 121 = 76 ∨ n % 121 = 87 ∨ n % 121 = 98 ∨ n % 121 = 109 ∨ n % 121 = 120 := by 
      omega
    rcases h7 with (h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7) <;> ( 
      norm_num [h7, pow_two, Int.add_emod, Int.mul_emod] at *
      all_goals
        omega
    )
  have h8 : (n ^ 2 + 2 * n + 12) % 121 = 0 := by 
    omega
  contradiction