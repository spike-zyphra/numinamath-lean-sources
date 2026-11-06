import Mathlib

/-Alison is eating 2401 grains of rice for lunch. She eats the rice in a very peculiar manner: every step, if she has only one grain of rice remaining, she eats it. Otherwise, she finds the smallest positive integer $d>1$ for which she can group the rice into equal groups of size $d$ with none left over. She then groups the rice into groups of size $d$, eats one grain from each group, and puts the rice back into a single pile. How many steps does it take her to finish all her rice?-/
theorem number_theory_610106 (a : ℕ → ℕ) (ha1 : a 0 = 2401) (ha2 : ∀ n ,a n = 1 → a (n + 1) = 0) (ha3 : ∀ n ,a n > 1 → ∃ m ,(IsLeast {m | 1 < m ∧ m ∣ a n} m) ∧ a (n + 1) = a n - a n / m) :
a 17 = 0 := by
  -- When count is a power of 7 (7^k), next step becomes 6*(7^(k-1))
  have h1 : ∀ n, (∃ k>0, a n = 7 ^ k) → a (n + 1) = a n / 7 * 6 := by
    intro n hn
    rcases hn with ⟨k, hk, hn⟩
    have hn' : a n > 1 := by
      rw [hn]; refine Nat.one_lt_pow (by linarith) (by simp)
    specialize ha3 n hn'
    rcases ha3 with ⟨m, hm, ha⟩
    -- Show 7 is the least divisor >1 for powers of 7
    have : IsLeast {m | 1 < m ∧ m ∣ a n} 7 := by
      simp [IsLeast, hn]
      constructor
      refine Dvd.dvd.pow (by simp) (by linarith)
      refine mem_lowerBounds.mpr ?_
      simp
      intro x hx hx'
      have : Nat.Prime 7 := by norm_num
      apply (Nat.dvd_prime_pow this).mp at hx'
      rcases hx' with ⟨p, hp, hp'⟩
      have hp'' : 1 ≤ p := by
        by_contra!
        interval_cases p
        simp [hp'] at hx
      rw [hp']; refine Bound.le_self_pow_of_pos (by simp) hp''
    apply (IsLeast.isLeast_iff_eq hm).mp at this
    rw [ha, hn, this]
    -- Calculate the remaining grains after eating
    refine (Nat.sub_eq_iff_eq_add ?_).mpr ?_
    exact Nat.div_le_self (7 ^ k) 7
    nth_rewrite 2 [← mul_one (7 ^ k / 7)]
    rw [← mul_add]
    norm_num
    refine Eq.symm (Nat.div_mul_cancel ?_)
    refine Dvd.dvd.pow (by simp) (by linarith)

  -- When count is 2*3*7^k, next step becomes 3*7^k
  have h2 : ∀ n, (∃ k, a n = 2 * 3 * 7 ^ k) → a (n + 1) = a n / 2 := by
    intro n hn
    rcases hn with ⟨k, hn⟩
    have hn' : a n > 1 := by
      rw [hn]
      have : 1 ≤ 7 ^ k := by exact Nat.one_le_pow' k 6
      nlinarith
    specialize ha3 n hn'
    rcases ha3 with ⟨m, hm, ha⟩
    -- Show 2 is the least divisor >1 for 2*3*7^k
    have : IsLeast {m | 1 < m ∧ m ∣ a n} 2 := by
      rw [IsLeast, hn]
      constructor
      simp
      refine (Nat.Prime.dvd_mul (by norm_num)).mpr (by left; norm_num)
      refine mem_lowerBounds.mpr ?_
      simp
      intro x hx hx'
      linarith
    apply (IsLeast.isLeast_iff_eq hm).mp at this
    rw [ha, hn, this]
    -- Calculate remaining grains
    refine (Nat.sub_eq_iff_eq_add ?_).mpr ?_
    exact Nat.div_le_self (2 * 3 * 7 ^ k) 2 
    rw [← mul_two]
    refine Eq.symm (Nat.div_mul_cancel ?_)
    rw [mul_assoc]; simp

  -- When count is 3*7^k, next step becomes 2*7^k
  have h3 : ∀ n, (∃ k, a n = 3 * 7 ^ k) → a (n + 1) = a n / 3 * 2 := by
    intro n hn
    rcases hn with ⟨k, hn⟩
    have hn' : a n > 1 := by
      rw [hn]
      have : 1 ≤ 7 ^ k := by exact Nat.one_le_pow' k 6
      nlinarith
    specialize ha3 n hn'
    rcases ha3 with ⟨m, hm, ha⟩
    -- Show 3 is the least divisor >1 for 3*7^k
    have : IsLeast {m | 1 < m ∧ m ∣ a n} 3 := by
      rw [IsLeast, hn]
      constructor
      simp
      refine mem_lowerBounds.mpr ?_
      simp
      intro x hx hx'
      by_cases h : x = 2
      · rw [h] at hx'
        apply (Nat.Prime.dvd_mul (by norm_num)).mp at hx'
        norm_num at hx'
        apply Nat.Prime.dvd_of_dvd_pow (by norm_num) at hx'
        norm_num at hx'
      omega
    apply (IsLeast.isLeast_iff_eq hm).mp at this
    rw [ha, hn, this]
    -- Calculate remaining grains
    refine (Nat.sub_eq_iff_eq_add ?_).mpr ?_
    exact Nat.div_le_self (3 * 7 ^ k) 3
    nth_rewrite 2 [← mul_one (3 * 7 ^ k / 3)]
    rw [← mul_add]
    norm_num
    exact Nat.mul_comm 3 (7 ^ k)

  -- When count is 2*7^k, next step becomes 7^k
  have h4 : ∀ n, (∃ k, a n = 2 * 7 ^ k) → a (n + 1) = a n / 2 := by
    intro n hn
    rcases hn with ⟨k, hn⟩
    have hn' : a n > 1 := by
      rw [hn]
      have : 1 ≤ 7 ^ k := by exact Nat.one_le_pow' k 6
      nlinarith
    specialize ha3 n hn'
    rcases ha3 with ⟨m, hm, ha⟩
    -- Show 2 is the least divisor >1 for 2*7^k
    have : IsLeast {m | 1 < m ∧ m ∣ a n} 2 := by
      rw [IsLeast, hn]
      constructor
      simp
      refine mem_lowerBounds.mpr ?_
      simp
      intro x hx hx'
      linarith
    apply (IsLeast.isLeast_iff_eq hm).mp at this
    rw [ha, hn, this]
    -- Calculate remaining grains
    refine (Nat.sub_eq_iff_eq_add ?_).mpr ?_
    exact Nat.div_le_self (2 * 7 ^ k) 2 
    rw [← mul_two]
    refine Eq.symm (Nat.div_mul_cancel ?_)
    simp

  -- Every 4 steps, a power of 7 reduces its exponent by 1
  have h5 : ∀ n, (∃ k>0, a n = 7 ^ k) → a (n + 4) = a n / 7 := by
    intro n hn
    rcases hn with ⟨k, hk, hn⟩
    specialize h1 n
    simp [hk, hn] at h1
    -- Step n+1: 7^k → 6*7^(k-1)
    have h1' : a (n + 1) = 2 * 3 * 7 ^ (k - 1) := by
      rw [h1]
      simp [mul_comm]
      refine Nat.div_eq_of_eq_mul_right (by simp) ?_
      refine Eq.symm (mul_pow_sub_one (by linarith) 7)
    -- Step n+2: 6*7^(k-1) → 3*7^(k-1)
    specialize h2 (n+1)
    simp [h1'] at h2
    have h2' : a (n+1+1) = 3 * 7 ^ (k - 1) := by
      rw [h2]
      refine Nat.div_eq_of_eq_mul_right (by simp) ?_
      ring
    -- Step n+3: 3*7^(k-1) → 2*7^(k-1)
    specialize h3 (n+1+1)
    simp [h2'] at h3
    rw [mul_comm] at h3
    -- Step n+4: 2*7^(k-1) → 7^(k-1)
    specialize h4 (n+1+1+1)
    simp [h3] at h4
    rw [add_assoc, add_assoc, add_assoc] at h4
    norm_num at h4
    rw [h4, hn]
    refine Eq.symm (Nat.div_eq_of_eq_mul_right (by simp) ?_)
    refine Eq.symm (mul_pow_sub_one (by linarith) 7)

  -- Initial state: 2401 = 7^4
  have h6 := h5 0
  simp at h6
  specialize h6 4
  -- After 4 steps: 343 = 7^3

  simp [ha1] at h6
  have h7 := h5 4
  simp at h7
  specialize h7 3
  -- After 8 steps: 49 = 7^2
  simp [h6] at h7 
  have h8 := h5 8
  simp at h8
  specialize h8 2
  -- After 12 steps: 7 = 7^1
  simp [h7] at h8 
  have h9 := h5 12
  simp at h9
  specialize h9 1
  -- After 16 steps: 1
  simp [h8] at h9 
  -- Final step: eat the last grain
  specialize ha2 16 h9
  simp at ha2
  exact ha2