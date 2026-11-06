import Mathlib

theorem algebra_21134 (x : ℕ) (hx : x > 0) (h : 2 * 2 ^ (x + 5) = 8 * 4 ^ x) :
    x = 3 := by 
  have eq1 : 2 * 2 ^ (x + 5) = 64 * (2 ^ x) := by
    ring_nf 
  have eq2 : 8 * 4 ^ x = 8 * (2 ^ (2 * x)) := by
    have h1 : 4 ^ x = 2 ^ (2 * x) := by 
      rw [show 4 = 2 ^ 2 by norm_num] 
      rw [← pow_mul]
    rw [h1] 
  have eq3 : 2 ^ (2 * x) = (2 ^ x) ^ 2 := by 
    ring_nf
  rw [eq1] at h 
  rw [eq2, eq3] at h 
  have eq4 : 64 * (2 ^ x) = 8 * ((2 ^ x) ^ 2) := by 
    linarith 
  have eq5 : (2 ^ x) = 8 := by
    have eq6 : 64 * (2 ^ x) = 8 * ((2 ^ x) ^ 2) := eq4 
    have h1 : (2 ^ x) > 0 := by 
      apply Nat.pow_pos 
      all_goals norm_num 
    nlinarith [sq_nonneg ((2 ^ x : ℕ) : ℕ), sq_nonneg ((8 : ℕ) : ℕ), 
      sq_pos_of_pos (show (0 : ℕ) < (2 : ℕ) by norm_num), 
      sq_nonneg ((2 ^ x : ℕ) - (8 : ℕ) : ℤ), 
      sq_nonneg ((2 ^ x : ℕ) : ℤ)
     ]
  have eq6 : x = 3 := by 
    have eq7 : (2 ^ x) = 8 := eq5 
    have eq8 : x = 3 := by 
      have eq9 : (2 ^ x) = (2 ^ 3) := by 
        rw [eq7]
        all_goals norm_num 
      have eq10 : x = 3 := by 
        exact Nat.pow_right_injective (by norm_num) eq9 
      exact eq10 
    exact eq8 
  exact eq6