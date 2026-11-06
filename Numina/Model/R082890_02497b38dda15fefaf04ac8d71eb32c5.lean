import Mathlib

theorem number_theory_108818 (n : ℕ) (h : 3^(6*n+12) + 9^(3*n+6) + 27^(2*n+4) = 3^(4*(n+3) + 255)) :
    (2^n + 3^n + 4^n + 7^n) % 5 = 2 := by
  have h1 : n = 127 := by 
    have eq1 : (9 : ℕ) ^ (3 * n + 6) = 3 ^ (6 * n + 12) := by 
      have h3 : (9 : ℕ) ^ (3 * n + 6) = 3 ^ (2 * (3 * n + 6)) := by 
        rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
        rw [← pow_mul]
        all_goals linarith 
      rw [h3]
      ring_nf
      <;> omega 
    have eq2 : (27 : ℕ) ^ (2 * n + 4) = 3 ^ (6 * n + 12) := by 
      have h4 : (27 : ℕ) ^ (2 * n + 4) = 3 ^ (3 * (2 * n + 4)) := by 
        rw [show (27 : ℕ) = 3 ^ 3 by norm_num]
        rw [← pow_mul]
        all_goals linarith 
      rw [h4]
      ring_nf
      <;> omega 
    have h_eq : (3 : ℕ) ^ (6 * n + 12) + (3 : ℕ) ^ (6 * n + 12) + (3 : ℕ) ^ (6 * n + 12) = 3 ^ (4 * (n + 3) + 255) := by
      calc 
        (3 : ℕ) ^ (6 * n + 12) + (3 : ℕ) ^ (6 * n + 12) + (3 : ℕ) ^ (6 * n + 12) = (3 : ℕ) ^ (6 * n + 12) + (9 : ℕ) ^ (3 * n + 6) + (27 : ℕ) ^ (2 * n + 4) := by 
          rw [eq1, eq2]
          all_goals linarith 
        _ = 3 ^ (4 * (n + 3) + 255) := by linarith [h] 
    have eq3 : (3 : ℕ) ^ (6 * n + 12) + (3 : ℕ) ^ (6 * n + 12) + (3 : ℕ) ^ (6 * n + 12) = 3 ^ (6 * n + 13) := by 
      calc 
        (3 : ℕ) ^ (6 * n + 12) + (3 : ℕ) ^ (6 * n + 12) + (3 : ℕ) ^ (6 * n + 12) = 3 * ((3 : ℕ) ^ (6 * n + 12)) := by 
          ring 
        _ = 3 ^ (6 * n + 13) := by 
          ring_nf 
          <;> omega 
    have eq4 : 3 ^ (6 * n + 13) = 3 ^ (4 * (n + 3) + 255) := by 
      linarith [eq3, h_eq] 
    have eq5 : 6 * n + 13 = 4 * (n + 3) + 255 := by 
      exact Nat.pow_right_injective (by norm_num) eq4 
    linarith 
  rw [h1]
  norm_num
  <;> native_decide 
  all_goals norm_num 
  <;> native_decide 
  all_goals norm_num
  <;> native_decide 
  all_goals norm_num
  <;> native_decide 
  all_goals norm_num