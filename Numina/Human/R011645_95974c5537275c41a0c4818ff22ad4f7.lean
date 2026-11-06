import Mathlib

/- If we divide number $19250$ with one number, we get remainder $11$. 
If we divide number $20302$ with the same number, we get the reamainder $3$. Which number is that? -/

theorem number_theory_34210 {n : ℕ} (h1 : 19250 % n = 11) (h2 : 20302 % n = 3) :
    n = 53 := by

  -- we first translate the conditions
      have r1:= h1
      have r2:= h2
      replace h1: n ∣ 19250 - 11 := by
        rw [← h1]
        apply Nat.dvd_sub_mod
      replace h2: n ∣ 20302 - 3 := by
        rw [← h2]
        apply Nat.dvd_sub_mod
      norm_num at h1 h2
      apply exists_eq_mul_right_of_dvd at h1
      obtain ⟨p, hp⟩ := h1
      apply exists_eq_mul_right_of_dvd at h2
      obtain ⟨q, hq⟩ := h2

    -- note that 20299 = 53 * 383, hence n = 1, 53, 383, 20299
      have d: n ∣ 20299 := by 
        rw [hq]
        simp
      replace d: n ∈ Nat.divisors 20299 := by
        simp
        exact d
      have eq: Nat.divisors 20299 = {1, 53, 383, 20299} := by 
        native_decide
      rw [eq] at d
      clear eq
      simp at d
      
      -- then we check the possible values of n
      rcases d with d | d | d | d

      -- n = 1
      .
        simp [d] at r1

      -- n = 53
      .
        exact d

      -- n = 383
      .
        simp [d] at *
      
      -- n = 20299
      .
        simp [d] at r1