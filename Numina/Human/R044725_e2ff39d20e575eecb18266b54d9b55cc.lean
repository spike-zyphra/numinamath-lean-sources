import Mathlib

/-Find all integers x such that 2x^2+x-6 is a positive integral power of a prime positive integer.-/
theorem algebra_608794: {x: ℤ | ∃ a: ℤ, (Prime a) ∧ (0 < a) ∧ (∃ n: ℕ, 1 ≤ n ∧ 2 * x ^ 2 + x - 6 = a ^ n)} = {-3,2,5} := by
  ext x
  constructor

  -- the foward direction --
  . intro h
    simp at h
    obtain ⟨a,hap,ha,n,hn,h⟩ := h
    simp
    have id: 2 * x ^ 2 + x - 6 = (2 * x - 3) * (x + 2) := by ring
    rw [id] at h
    clear id
    by_contra! rr -- for convenience, we assume the contrary --
    -- we show we must have a ∣ 2 * x - 3 --
    have d1: a ∣ 2 * x - 3 := by
       rw [show (a: ℤ) ^ n = 1 * a ^ n by ring] at h
       apply mul_eq_mul_prime_pow hap at h
       obtain ⟨i,j,b,c,hij,hbc,hb,hc⟩ := h
       by_cases t: 1 ≤ i
       . rw [hb]
         have o: a ∣ a ^ i := by
            apply dvd_pow_self
            omega
         have s: a ^ i ∣ b * a ^ i := by
            apply dvd_mul_left
         apply dvd_trans o s
       . simp at t
         simp [t] at hb
         by_cases ss: 0 ≤ b
         . symm at hbc
           have l:= hbc
           apply Int.eq_one_of_mul_eq_one_right at hbc
           simp [hbc] at l
           simp [l] at hc
           simp [hbc] at hb
           replace hb : x = 2 := by omega
           omega
           exact ss
         . simp at ss
           set u:= -b with hu
           replace hu: b = -u := by simp [hu]
           set v:= -c with hv
           replace hv: c = -v := by simp [hv]
           simp [hu,hv] at hbc
           symm at hbc
           have l:= hbc
           apply Int.eq_one_of_mul_eq_one_right at hbc
           simp [hbc] at hu
           simp [hu] at hb
           simp [hbc] at l
           simp [l] at hv
           simp [hv] at hc
           replace hb: x = 1 := by omega
           simp [hb] at hc
           have contra: -a ^ j ≤ 0 := by
             have o: 0 ≤ a ^ j := by
              apply Nonneg.pow_nonneg
              omega
             omega
           rw [← hc] at contra
           tauto
           omega
    -- we show we must have a ∣ x + 2, which is similar as above --
    have d2: a ∣ x + 2 := by
       rw [show (a: ℤ) ^ n = 1 * a ^ n by ring] at h
       apply mul_eq_mul_prime_pow hap at h
       obtain ⟨i,j,b,c,hij,hbc,hb,hc⟩ := h
       by_cases t: 1 ≤ j
       . rw [hc]
         have o: a ∣ a ^ j := by
            apply dvd_pow_self
            omega
         have s: a ^ j ∣ c * a ^ j := by
            apply dvd_mul_left
         apply dvd_trans o s
       . simp at t
         simp [t] at hc
         by_cases ss: 0 ≤ b
         . symm at hbc
           have l:= hbc
           apply Int.eq_one_of_mul_eq_one_right at hbc
           simp [hbc] at l
           simp [l] at hc
           simp [hbc] at hb
           replace hc : x = -1 := by omega
           simp [hc] at hb
           have q: 0 ≤ a ^ i := by
             apply Nonneg.pow_nonneg
             omega
           rw [← hb] at q
           tauto
           exact ss
         . simp at ss
           set u:= -b with hu
           replace hu: b = -u := by simp [hu]
           set v:= -c with hv
           replace hv: c = -v := by simp [hv]
           simp [hu,hv] at hbc
           symm at hbc
           have l:= hbc
           apply Int.eq_one_of_mul_eq_one_right at hbc
           simp [hbc] at hu
           simp [hu] at hb
           simp [hbc] at l
           simp [l] at hv
           simp [hv] at hc
           replace hb: x = 1 := by omega
           simp [hb] at hc
           have contra: -a ^ j ≤ 0 := by
             have o: 0 ≤ a ^ j := by
              apply Nonneg.pow_nonneg
              omega
             omega
           omega
     -- now we show the key dvd --
    have d3: a ∣ 7 := by
      rw [show 7 = 2 * (x + 2) - (2 * x - 3) by ring]
      replace d2: a ∣ 2 * (x + 2) := by
        have o: x + 2 ∣ 2 * (x + 2) := by
          apply dvd_mul_left
        apply dvd_trans d2 o
      apply Int.dvd_sub d2 d1
    -- now we show that a = 7 --
    have a_val: a = 7 := by
      have o: a.natAbs ∣ 7 := by
        rw [← Int.natAbs_dvd_natAbs] at d3
        simp at d3
        exact d3
      have hp: Nat.Prime 7 := by norm_num
      rw [Nat.Prime.dvd_iff_eq hp] at o
      omega
      by_contra! no
      replace no: a = 1 ∨ a = -1 := by omega
      rcases no with no | no
      . rw [no] at hap
        absurd hap
        norm_num
      . rw [no] at ha
        omega
      -- now we show that 2x-3 = 7 ^n or 2x-3 = -7 ^ n --
    simp [a_val] at *
    clear d1 d2
    have H:= h
    rw [show (7: ℤ) ^ n = 1 * 7 ^ n by ring] at H
    replace hap: Prime (7: ℤ) := by norm_num
    apply mul_eq_mul_prime_pow hap at H
    obtain ⟨i,j,b,c,hij,hbc,hb,hc⟩ := H
    clear hap
    by_cases rb: 0 ≤ b
    -- case 1: 0 ≤ b, then b = 1--
    . symm at hbc
      have l:= hbc
      apply Int.eq_one_of_mul_eq_one_right at hbc
      simp [hbc] at l
      simp [l] at hc
      simp [hbc] at hb
      clear hbc rb d3 a_val ha h hn
      by_cases o: 2 ≤ i
      -- for the cases 2 ≤ i, we must have j ≤ 1 --
      . have j_val: j < 2 := by
          by_contra! no
          replace hc: 7 ^ 2 ∣ x + 2 := by
            rw [hc]
            apply pow_dvd_pow
            exact no
          replace hb: 7 ^ 2 ∣ 2 * x - 3 := by
            rw [hb]
            apply pow_dvd_pow
            exact o
          have contra: 7 ^ 2 ∣ (7: ℤ) := by
            nth_rewrite 2[show (7: ℤ)  = 2 * (x + 2) - (2 * x - 3) by ring]
            replace hc: 7 ^ 2 ∣ 2 * (x + 2) := by
              have f: x + 2 ∣ 2 * (x + 2) := by
                apply dvd_mul_left
              apply dvd_trans hc f
            apply Int.dvd_sub hc hb
          omega
        replace j_val: j = 0 ∨ j = 1 := by omega
        rcases j_val with j_val | j_val
        . simp [j_val] at hc
          replace hc: x = -1 := by omega
          simp [hc] at hb
          have v: (7: ℤ) ∣ 7 ^ i := by
            apply dvd_pow_self
            omega
          rw [← hb] at v
          omega
        . simp [j_val] at hc
          omega
     -- for the cases i = 0 or 1 --
      . replace o: i = 0 ∨ i = 1 := by omega
        rcases o with o | o
        . simp [o] at hb
          replace hb: x = 2 := by omega
          omega
        . simp [o] at hb
          replace hb: x = 5 := by omega
          omega
      exact rb
   -- case 2: 0 > b, then b = -1 --
    . simp at rb
      set u:= -b with hu
      replace hu: b = -u := by simp [hu]
      set v:= -c with hv
      replace hv: c = -v := by simp [hv]
      simp [hu,hv] at hbc
      symm at hbc
      have l:= hbc
      apply Int.eq_one_of_mul_eq_one_right at hbc
      simp [hbc] at hu
      simp [hu] at hb
      simp [hbc] at l
      simp [l] at hv
      simp [hv] at hc
      clear hij hu hv l hbc rb d3 a_val ha hn
      by_cases o: 2 ≤ i
      -- for the cases 2 ≤ i, we must have j ≤ 1 --
      . have j_val: j < 2 := by
          by_contra! no
          replace hc: 7 ^ 2 ∣ x + 2 := by
            rw [hc]
            rw [Int.dvd_neg]
            apply pow_dvd_pow
            exact no
          replace hb: 7 ^ 2 ∣ 2 * x - 3 := by
            rw [hb]
            rw [Int.dvd_neg]
            apply pow_dvd_pow
            exact o
          have contra: 7 ^ 2 ∣ (7: ℤ) := by
            nth_rewrite 2[show (7: ℤ)  = 2 * (x + 2) - (2 * x - 3) by ring]
            replace hc: 7 ^ 2 ∣ 2 * (x + 2) := by
              have f: x + 2 ∣ 2 * (x + 2) := by
                apply dvd_mul_left
              apply dvd_trans hc f
            apply Int.dvd_sub hc hb
          omega
        replace j_val: j = 0 ∨ j = 1 := by omega
        rcases j_val with j_val | j_val
        . simp [j_val] at hc
          replace hc: x = -3 := by omega
          omega
        . simp [j_val] at hc
          replace hc: x = -9 := by omega
          simp [hc] at hb
          have il: i < 2 := by
            by_contra! no
            have contra: 7 ^ 2 ≤ (21: ℤ)  := by
              rw [hb]
              rw [pow_le_pow_iff_right₀]
              exact no
              norm_num
            tauto
          replace il : i ≤ 1 := by omega
          have contra: (21: ℤ) ≤ 7 ^ 1 := by
            rw [hb]
            rw [pow_le_pow_iff_right₀]
            exact il
            norm_num
          tauto
     -- for the cases i = 0 or 1 --
      . replace o: i = 0 ∨ i = 1 := by omega
        rcases o with o | o
        . simp [o] at hb
          replace hb: x = 1 := by omega
          simp [hb] at hc
          have v: (7: ℤ) ∣ -7 ^ j := by
            rw [Int.dvd_neg]
            apply dvd_pow_self
            by_contra! no
            simp [no] at hc
          rw [←hc] at v
          omega
        . simp [o] at hb
          replace hb: x = -2 := by omega
          simp [hb] at hc
      omega


  -- the backward direction --
  . intro h
    simp at h
    simp
    rcases h with h | h | h
    -- x = -3 --
    . simp [h]
      use 3
      simp
      norm_num
      use 2
      simp
    -- x = 2 --
    . simp [h]
      use 2
      simp
      norm_num
      use 2
      simp
    -- x = 5 --
    . simp [h]
      use 7
      simp
      norm_num
      use 2
      simp
