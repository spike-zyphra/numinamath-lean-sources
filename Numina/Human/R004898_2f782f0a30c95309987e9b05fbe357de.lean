import Mathlib

/- Es sei $p>7$ eine Primzahl, die bei Division durch 6 den Rest 1 lässt. Setze $m=2^{p}-1$. Man beweise, dass $2^{m-1}-1$ ohne Rest durch $127 m$ teilbar ist. -/
theorem number_theory_604490 (p : ℕ) (hp : Nat.Prime p) (h : p > 7)
    (h1 : p % 6 = 1) (m : ℕ) (hm : m = 2 ^ p - 1) :
    (2 ^ (m - 1) - 1) % (127 * m) = 0 := by

    -- some basic facts about p and m.
    let a := 127
    have : 2^7 < 2^p := by apply pow_lt_pow_right₀; norm_num; assumption
    have : 10 < 2^p := by linarith
    have : 2^6 < 2^(p-1) := by apply pow_lt_pow_right₀; linarith; omega
    have : 3 < m := by simp_all; omega

    -- prove that 127 ∣ 2^(m-1)-1 using congruence relation.
    have tmp1 : a ∣ 2^(m-1) - 1 := by
      have : 7∣ m-1 := by
        have t1: 7 ∣ 2^p -2 := by
          have tmp : 7 ∣ 2^6 -1 := by norm_num
          have tmp2 : 2^6 ≡ 1 [MOD 7] := by exact rfl
          have pmod61 : 6 ∣ p -1 := by refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm h1)); linarith
          obtain ⟨d,hd⟩ := pmod61
          have peq : p = 6*d +1 := by rw [<-hd]; omega
          have : 2^p = 2^(6*d+1) := by rw [peq]   
          rw [this] 
          have : 2^(6*d+1) = (2^6)^d * 2 := by rw [Nat.pow_add_one]; rw[Nat.pow_mul]
          rw [this]
          have : (2^6)^d ≡ 1^d [MOD 7] := by exact Nat.ModEq.pow d tmp2
          have : (2^6)^d ≡ 1 [MOD 7] := by ring_nf at this; assumption
          have : (2^6)^d*2 ≡ 1*2 [MOD 7] := by exact Nat.ModEq.mul this rfl
          have : (2^6)^d*2 ≡ 2 [MOD 7] := by ring_nf at this; assumption
          have : ((2 ^ 6) ^ d * 2 - 2) % 7 = 0 := by exact Nat.sub_mod_eq_zero_of_mod_eq this
          have : 7 ∣ ((2^6)^d*2 -2 ) := by exact Nat.dvd_of_mod_eq_zero this
          assumption

        have t2: 2^p-2 = m - 1 := by simp [hm]; exact rfl
        rw [t2] at t1
        assumption

      have : 2^(m-1) % a = 1 := by 
        have two71: 2^7 % 127 = 1 := by norm_num
        have : 2^7 ≡ 1 [MOD 127] := by exact rfl
        have : ((m-1)/7)*7 = m-1 := by refine Nat.div_mul_cancel ?_; assumption 
        have : 2^(m-1) = (2^7) ^ ((m-1)/7) := by rw [←pow_mul]; rw [mul_comm]; rw [this]
        rw [this]; rw [Nat.pow_mod]
        rw [two71]; field_simp
      have : (2^(m-1)-1) % a = 0 := by exact Nat.sub_mod_eq_zero_of_mod_eq this
      exact Nat.dvd_of_mod_eq_zero this

    -- prove that m ∣ 2^(m-1) -1.
    have tmp2 : m ∣ 2^(m-1)-1 := by
      have : p ∣ (m-1) := by
        have ptot : p.totient = p-1 := by exact Nat.totient_prime hp
        have pcop2 : Nat.Coprime 2 p := by
          refine (Nat.Prime.coprime_iff_not_dvd ?_).mpr ?_;
          norm_num
          by_contra twodivp
          have : 2 = p := by rw [← Nat.dvd_prime_two_le]; assumption; assumption; norm_num
          linarith
        have : 2 ^ p.totient ≡ 1 [MOD p] := by exact Nat.ModEq.pow_totient pcop2
        rw [ptot] at this;
        have fermat: 2 * 2 ^ (p - 1) ≡ 2 * 1 [MOD p] := by exact Nat.ModEq.mul rfl this
        have t1 : 2 * 2 ^ (p - 1) = 2^p := by refine mul_pow_sub_one ?_ 2; exact Nat.not_eq_zero_of_lt h
        rw [t1] at fermat; ring_nf at fermat

        have : p ∣ 2^p -2 := by refine (Nat.modEq_iff_dvd' ?_).mp (id (Nat.ModEq.symm fermat)); linarith
        simp [hm]; ring_nf; assumption

      obtain ⟨d, hd⟩ := this
      have : 2 ^ p % m = 1 := by
        have : m ∣ 2^p - 2^p % m := by exact Nat.dvd_sub_mod (2 ^ p)
        have : m ≤ 2^p - 2^p % m := by
          zify; rw [Int.le_iff_pos_of_dvd];
          norm_cast; field_simp;
          have : 2^p % m + m * (2^p / m) = 2^p := by exact Nat.mod_add_div (2^p) m
          have : 0 < (2^p / m) := by refine Nat.div_pos ?_ ?_; simp [hm]; linarith
          have : 0 < m * (2^p / m) := by nlinarith
          linarith
          norm_cast; linarith
          norm_cast;
        have : 2 ^ p % m ≤ 1 := by
          nth_rw 1 [hm] at this
          omega
        have : 2 ^ p % m ≠ 0 := by
          by_contra t1
          have t2: m ∣ 2^p := by exact Nat.dvd_of_mod_eq_zero t1
          have t3: m < 2^p := by rw [hm]; omega
          have t4: m ∣ m := by exact Nat.dvd_refl m
          have t5: m ∣ 2^p - m := by exact Nat.dvd_sub' t2 t4
          have : m ∣ 1 := by
            have : 2^p - m = 1 := by rw [hm]; omega
            rw [this] at t5; assumption
          have : m = 1 := by exact Nat.eq_one_of_dvd_one this
          linarith

        have : 1 ≤ 2^p %m := by exact Nat.one_le_iff_ne_zero.mpr this
        linarith

      have : (2^p)^d % m = 1 := by rw [Nat.pow_mod]; rw [this]; ring_nf; refine Nat.mod_eq_of_lt ?_; linarith
      have : 2^(p*d) % m = 1 := by rw [←pow_mul] at this; assumption
      rw [hd]
      have : (2^(p*d) - 1) % m = 0 := by
        have : 1 % m = 1 := by refine Nat.mod_eq_of_lt ?_; linarith
        refine Nat.sub_mod_eq_zero_of_mod_eq ?_; linarith
      exact Nat.dvd_of_mod_eq_zero this

    -- provethat 127 and m are coprime, then we can finish the proof that 127m divides 2^(m-1)-1.
    have : Nat.Coprime a m := by
        have prima: Nat.Prime a := by norm_num;
        have prim7 : Prime 7 := by rw [← Nat.prime_iff]; norm_num
        have : ¬ (a ∣ m) := by
          by_contra advdm
          simp [a,hm] at advdm
          have : 7 ∣ p := by
            have tmp3 : 2^p % 127 = 1 := by
              refine Nat.mod_eq_of_modEq ?_ ?_
              rw [Nat.modEq_iff_dvd]
              rw [← Int.dvd_neg]
              zify at advdm; simp_all
              linarith
            have tmp4 : 2^7 % a = 1 := by norm_num
            have : p % 7 = 0 := by
              by_contra tmp5
              have pmod7pos : 0 < p % 7 := by exact Nat.zero_lt_of_ne_zero tmp5
              have pmod7lt : p % 7 < 7 := by refine Nat.mod_lt p ?_; linarith
              have myeq : p % 7 + 7 * (p/7) = p := by exact Nat.mod_add_div p 7
              rw [← myeq] at tmp3; rw [pow_add] at tmp3
              have powpmod7: 2^(p % 7) %127 = 1 := by
                have tmp6: (2 ^ (7 * (p / 7))) % 127 = 1 := by
                  rw [pow_mul]; rw [Nat.pow_mod]; rw [tmp4]; ring_nf; 
                have : 2 ^ (7 * (p / 7)) * 2 ^ (p % 7)  % 127 = 2 ^ (7 * (p / 7)) % 127 * 2 ^ (p % 7)  % 127 := by exact Eq.symm Nat.mod_mul_mod
                have : 2 ^ (7 * (p / 7)) % 127 * 2 ^ (p % 7)  % 127 = 1 := by rw [mul_comm] at tmp3; rw [tmp3] at this; symm; assumption
                rw [tmp6] at this; ring_nf at this; assumption
              by_cases pmod7eq1 : p % 7 = 1;
                rw [pmod7eq1] at powpmod7; norm_num at powpmod7
              by_cases pmod7eq2 : p % 7 = 2;
                rw [pmod7eq2] at powpmod7; norm_num at powpmod7
              by_cases pmod7eq3 : p % 7 = 3;
                rw [pmod7eq3] at powpmod7; norm_num at powpmod7
              by_cases pmod7eq4 : p % 7 = 4;
                rw [pmod7eq4] at powpmod7; norm_num at powpmod7
              by_cases pmod7eq5 : p % 7 = 5;
                rw [pmod7eq5] at powpmod7; norm_num at powpmod7
              by_cases pmod7eq6 : p % 7 = 6;
                rw [pmod7eq6] at powpmod7; norm_num at powpmod7
              omega

            exact Nat.dvd_of_mod_eq_zero this

          have : 7 = p := by rw [← prime_dvd_prime_iff_eq]; assumption; assumption; exact Nat.prime_iff.mp hp
          linarith
        have : a.Coprime m ∨ (a ∣ m) := by exact Nat.coprime_or_dvd_of_prime prima m
        have : a.Coprime m := by tauto
        simp_all; assumption


    have : a * m ∣ 2^(m-1) -1 := by apply Nat.Coprime.mul_dvd_of_dvd_of_dvd; repeat assumption
    exact Nat.dvd_iff_mod_eq_zero.mp this
