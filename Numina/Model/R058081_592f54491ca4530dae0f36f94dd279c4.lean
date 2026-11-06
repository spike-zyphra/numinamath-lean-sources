import Mathlib

theorem algebra_9756 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + 2 * x * y + 3 * x * y * z = 115) : x + y + z = 10 ∨ x + y + z = 16 := by
  -- We need to prove x + y + z = 10 or 16.
  -- First, we can rewrite the equation as x(1 + 2*y + 3*y*z) = 115
  have h1 : x ∣ 115 := by
    use 1 + 2 * y + 3 * y * z 
    nlinarith 
  -- We know x is a divisor of 115
  -- The prime factors of 115 are 5 and 23
  -- So the possible values for x are 1, 5, 23, 115 
  have h2 : x = 1 ∨ x = 5 ∨ x = 23 ∨ x = 115 := by
    have h2 : x ∣ 115 := h1
    have h3 : x ≤ 115 := by
      exact Nat.le_of_dvd (by norm_num) h2
    interval_cases x <;> norm_num at h2 ⊢ <;> tauto
  rcases h2 with h2 | h2 | h2 | h2
  · -- Now we have x = 1
    rw [h2] at h
    have h3 : 2 * y + 3 * y * z = 114 := by
      nlinarith 
    -- We need to find divisors of 114
    have h4 : y ∣ 114 := by
      use 3 * z + 2
      nlinarith 
    have h5 : y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 6 ∨ y = 19 ∨ y = 38 ∨ y = 57 ∨ y = 114 := by
      have h5 : y ∣ 114 := h4
      have h6 : y ≤ 114 := by
        exact Nat.le_of_dvd (by norm_num) h5
      interval_cases y <;> norm_num at h5 ⊢ <;> tauto 
    rcases h5 with h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5
    · -- y = 1
      rw [h5] at h3
      omega 
    · -- y = 2
      rw [h5] at h3
      omega 
    · -- y = 3
      rw [h5] at h3
      -- z should be 12
      have : z = 12 := by
        nlinarith 
      rw [show y = 3 by linarith, show z = 12 by linarith, show x = 1 by linarith]
      right 
      norm_num 
    · -- y = 6
      rw [h5] at h3
      omega 
    · -- y = 19
      rw [h5] at h3
      omega 
    · -- y = 38
      rw [h5] at h3
      omega 
    · -- y = 57
      rw [h5] at h3
      omega 
    · -- y = 114
      rw [h5] at h3
      omega 
  · -- Now we have x = 5
    rw [h2] at h
    have h3 : 2 * y + 3 * y * z = 22 := by
      nlinarith 
    -- We need to find divisors of 22
    have h4 : y ∣ 22 := by
      use 3 * z + 2
      nlinarith 
    have h5 : y = 1 ∨ y = 2 ∨ y = 11 ∨ y = 22 := by
      have h5 : y ∣ 22 := h4
      have h6 : y ≤ 22 := by
        exact Nat.le_of_dvd (by norm_num) h5
      interval_cases y <;> norm_num at h5 ⊢ <;> tauto 
    rcases h5 with h5 | h5 | h5 | h5
    · -- y = 1
      rw [h5] at h3
      omega 
    · -- y = 2
      rw [h5] at h3
      -- z should be 3
      have : z = 3 := by
        nlinarith 
      rw [show y = 2 by linarith, show z = 3 by linarith, show x = 5 by linarith]
      left 
      norm_num 
    · -- y = 11
      rw [h5] at h3
      omega 
    · -- y = 22
      rw [h5] at h3
      omega 
  · -- Now we have x = 23
    rw [h2] at h 
    -- This gives us a contradiction 
    nlinarith [show 0 < y from hy, show 0 < z from hz] 
  · -- Now we have x = 115
    rw [h2] at h 
    -- This gives us a contradiction
    nlinarith [show 0 < y from hy, show 0 < z from hz]