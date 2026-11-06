import Mathlib

theorem algebra_21542 {x : ℤ} (h : 63 ∣ x ∧ x ∣ 63) :
    x * (-x) = -3969 := by
  rcases h with ⟨h1, h2⟩
  -- 63 divides x, so x divides 63
  -- Let's write x = 63k
  rcases h1 with ⟨k, hk⟩
  -- Substitute into x divides 63
  rw [hk] at h2
  -- So 63 * k divides 63
  -- Therefore, exists some integer m such that 63 = (63 * k) * m
  rcases h2 with ⟨m, hm⟩
  -- 63 = 63 * k * m
  -- Therefore, moving 63 to right side.
  -- 63 - 63 * k * m = 0
  -- 63 * (1 - k * m) = 0
  -- Since 63 ≠ 0, so 1 - k * m = 0, so k * m = 1
  have h8 : k * m = 1 := by
    nlinarith
  -- Then from k * m = 1, k is either 1 or -1
  have h9 : k = 1 ∨ k = -1 := by
    have h10 : k ∣ 1 := by
      use m 
      all_goals linarith
    have : k = 1 ∨ k = -1 := by 
      have h7 : k ∣ 1 := h10
      have h8 : k ≤ 1 := by 
        apply Int.le_of_dvd (by norm_num) h7 
      have h9 : k ≥ -1 := by 
        have h7' : (-k) ∣ 1 := by 
          exact Int.neg_dvd.2 h7 
        have h8' : -k ≤ 1 := by 
          apply Int.le_of_dvd (by norm_num) h7' 
        omega 
      interval_cases k <;> tauto 
    assumption
  rcases h9 with (h9 | h9)
  · -- k = 1
    rw [show k = 1 by linarith] at hk 
    have h5 : x = 63 := by linarith
    rw [h5]
    all_goals norm_num
  · -- k = -1
    rw [show k = -1 by linarith] at hk 
    have h5 : x = -63 := by linarith
    rw [h5]
    all_goals norm_num