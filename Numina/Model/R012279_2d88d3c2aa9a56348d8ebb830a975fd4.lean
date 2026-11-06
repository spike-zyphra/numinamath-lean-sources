import Mathlib

theorem number_theory_93816 {n : ℕ} (hn : n ≠ 0) (h1 : Nat.lcm n 18 = 180) (h2 : Nat.gcd n 45 = 15) :
    (Nat.digits 10 n).sum = 6 := by 
  have n15 : 15 ∣ n := by
    have h4 : n.gcd 45 = 15 := h2 
    have h5 : 15 ∣ n := by
      have h6 : n.gcd 45 ∣ n := by 
        apply Nat.gcd_dvd_left 
      rw [show n.gcd 45 = 15 by exact h4] at h6 
      exact h6 
    exact h5

  have h4 : n ∣ 180 := by
    have h3' : n ∣ Nat.lcm n 18 := by 
      exact Nat.dvd_lcm_left n 18 
    rw [h1] at h3'
    exact h3'

  have h5 : n ≤ 180 := by
    exact Nat.le_of_dvd (show 0 < (180 : ℕ) by norm_num) h4

  have h7 : n % 15 = 0 := by 
    omega

  have h8 : n % 4 = 0 := by 
    by_contra h7 
    push_neg at h7
    have h10 : n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by 
      omega 
    rcases h10 with (h10 | h10 | h10)
    · -- Assume n % 4 = 1 
      -- This case leads to contradiction since lcm(n,18) not 180 for n
      have h11 : Nat.lcm n 18 = 180 := h1 
      have h12 : n % 4 = 1 := h10 
      have h5' : n ≤ 180 := h5 
      interval_cases n <;> norm_num [Nat.lcm, Nat.gcd] at h1 h2 h11 h12 ⊢ 
    · -- Assume n % 4 = 2 
      -- This case leads to contradiction since lcm(n,18) not 180 for n
      have h11 : Nat.lcm n 18 = 180 := h1 
      have h12 : n % 4 = 2 := h10 
      have h5' : n ≤ 180 := h5 
      interval_cases n <;> norm_num [Nat.lcm, Nat.gcd] at h1 h2 h11 h12 ⊢ 
    · -- Assume n % 4 = 3 
      -- This case leads to contradiction since lcm(n,18) not 180 for n 
      have h11 : Nat.lcm n 18 = 180 := h1 
      have h12 : n % 4 = 3 := h10 
      have h5' : n ≤ 180 := h5 
      interval_cases n <;> norm_num [Nat.lcm, Nat.gcd] at h1 h2 h11 h12 ⊢

  have h9 : n % 5 = 0 := by
    by_contra h7 
    push_neg at h7 
    have h11 : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by 
      omega 
    rcases h11 with (h11 | h11 | h11 | h11) 
    · -- Assume n % 5 = 1 
      -- This case leads to contradiction since lcm(n,18) not 180 for n 
      have h11' : Nat.lcm n 18 = 180 := h1 
      have h12 : n % 5 = 1 := h11 
      have h5' : n ≤ 180 := h5 
      interval_cases n <;> norm_num [Nat.lcm, Nat.gcd] at h1 h2 h11' h12 ⊢ 
    · -- Assume n % 5 = 2 
      -- This case leads to contradiction since lcm(n,18) not 180 for n 
      have h11' : Nat.lcm n 18 = 180 := h1 
      have h12 : n % 5 = 2 := h11 
      have h5' : n ≤ 180 := h5 
      interval_cases n <;> norm_num [Nat.lcm, Nat.gcd] at h1 h2 h11' h12 ⊢ 
    · -- Assume n % 5 = 3 
      -- This case leads to contradiction since lcm(n,18) not 180 for n 
      have h11' : Nat.lcm n 18 = 180 := h1 
      have h12 : n % 5 = 3 := h11 
      have h5' : n ≤ 180 := h5 
      interval_cases n <;> norm_num [Nat.lcm, Nat.gcd] at h1 h2 h11' h12 ⊢ 
    · -- Assume n % 5 = 4 
      -- This case leads to contradiction since lcm(n,18) not 180 for n 
      have h11' : Nat.lcm n 18 = 180 := h1 
      have h12 : n % 5 = 4 := h11 
      have h5' : n ≤ 180 := h5 
      interval_cases n <;> norm_num [Nat.lcm, Nat.gcd] at h1 h2 h11' h12 ⊢

  have h10 : n = 60 := by
    have h11 : n % 4 = 0 := h8
    have h12 : n % 5 = 0 := h9 
    have h13 : n % 3 = 0 := by
      omega
    have h30 : n ≤ 180 := h5 
    interval_cases n <;> norm_num [Nat.lcm, Nat.gcd] at h1 h2 ⊢
  rw [h10]
  all_goals norm_num