import Mathlib

/-The greatest common divisor of two positive integers less than $100$ is equal to $3$. Their least common multiple is twelve times one of the integers. What is the largest possible sum of the two integers?-/
theorem number_theory_22704 :
    IsGreatest {x | ∃ a b : ℕ, 0 < a ∧ a < 100 ∧ 0 < b ∧ b < 100 ∧ x = a + b ∧ Nat.gcd a b = 3 ∧ Nat.lcm a b = 12 * a} 129 := by
  simp [IsGreatest, upperBounds]
  -- divide the problem into two parts
  refine ⟨?_, ?_⟩
  -- when a = 93, b = 36, the sum is 129
  . use 93
    norm_num
    use 36
    norm_num
  -- show the main part of the conclusion
  . intro x a ha1 ha2 b hb1 hb2 hx hgcd hlcm
    -- show a * b = 36 * a by Nat.gcd_mul_lcm
    have eq1 : a * b = 36 * a := by
      calc
        a * b = a.gcd b * a.lcm b := by rw [Nat.gcd_mul_lcm a b]
        _ = 3 * (12 * a) := by rw [hgcd, hlcm]
        _ = 36 * a := by ring_nf
    -- show b = 36, by a * b = 36 * a
    have hb : b = 36 := by
      calc
        b = a * b / a := by field_simp
        _ = 36 * a / a := by rw [eq1]
        _ = 36 := by field_simp
    clear hb1 hb2
    -- show that 3 ∣ a
    have ha_dvd : 3 ∣ a := by 
      rw [← hgcd]
      apply Nat.gcd_dvd_left
    -- by division algorithm, a = 3k
    obtain ⟨k, hk⟩ := ha_dvd
    -- show that k ≤ 33
    have hk2 : k ≤ 33 := by
      replace ha2 : a ≤ 99 := by apply Nat.le_of_lt_succ; simp; exact ha2
      calc
        k = a / 3 := by rw [hk]; field_simp
        _ ≤ 33 := by apply Nat.div_le_of_le_mul; linarith only [ha2]
    -- show that k > 0
    have hk1 : 0 < k := by 
      contrapose! ha1
      have hk' : k = 0 := by linarith only [ha1]
      rw [hk, hk']
    clear ha1 ha2
    -- show that k = 33 ∨ k = 32 ∨ k ≤ 31 (the first and the second cases are contradiction)
    have hk : k = 33 ∨ k = 32 ∨ k ≤ 31 := by
      set k' := 33 - k with hk'
      match k' with
      | 0 => -- show that k = 33, when k' = 0
        have _ : k = 33 := by
          calc
           k = 33 - (33 - k) := by rw [Nat.sub_sub_eq_min]; simp [hk2]
           _ = 33 := by rw [<-hk']
        tauto
      | 1 => -- show that k = 32, when k' = 1
        have _ : k = 32 := by
          calc
           k = 33 - (33 - k) := by rw [Nat.sub_sub_eq_min]; simp [hk2]
           _ = 32 := by rw [<-hk']
        tauto
      | m + 2 => -- show that k ≤ 31, when k' ≥ 2
        have _ : k ≤ 31 := by
          calc
           k = 33 - (33 - k) := by rw [Nat.sub_sub_eq_min]; simp [hk2]
           _ = 33 - (m + 2) := by rw [<-hk']
           _ ≤ 31 := by rw [<-Nat.sub_sub]; norm_num
        tauto
    -- show that x ≤ 129 by three cases
    rcases hk with hk33 | hk32 | hk31
    -- when k = 33
    . rw [hk33] at hk
      rw [hk, hb] at hgcd
      norm_num at hgcd
    -- when k = 32
    . rw [hk32] at hk
      rw [hk, hb] at hgcd
      norm_num at hgcd
    -- when k ≤ 31, obviously 
    . calc
        x = a + b := by rw [hx]
        _ ≤ 93 + 36 := by rw [hb]; apply Nat.add_le_add_right; rw [hk]; linarith
  