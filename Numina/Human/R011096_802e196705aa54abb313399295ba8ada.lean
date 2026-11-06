import Mathlib

/- 2. Find all triples of natural numbers $a, b$, and $c$, for which the numbers $a^{2}-23$ and $b^{2}-23$ are prime and $\left(a^{2}-23\right)\left(b^{2}-23\right)=c^{2}-23$. -/
theorem number_theory_228293 (a b c : ℤ) (hapos : 0 ≤ a) (haprimepos : 0 < a^2 - 23) (hbpos : 0 ≤ b) (hbprimepos : 0 < b^2 - 23) (hcpos : 0 ≤ c) : (Prime (a^2 - 23) ∧ Prime (b^2 - 23) ∧ (a^2 - 23) * (b^2 - 23) = c^2 - 23) ↔ (a = 5 ∧ b = 6 ∧ c = 7) ∨ (a = 6 ∧ b = 5 ∧ c = 7) := by
  constructor
--First of all we solve the equation.
  · intro h
    obtain ⟨ha, hb, eq⟩ := h
--We first observe that a and b are both greater than or equal to 5, since a ^ 2 - 23 and b ^ 2 - 23 are prime numbers greater than 0.
    have lb : 5 ≤ a ∧ 5 ≤ b := by
      constructor
      · by_contra! hle
        interval_cases a
        all_goals omega
      · by_contra! hle
        interval_cases b
        all_goals omega
--We deduce that also c ^ 2 - 23 is positive.
    have hcpos : 0 < c ^ 2 - 23 := by
      rw [← eq, mul_pos_iff]
      omega
--We prove that a and b are not both 5, since otherwise we would have c ^ 2 = 27, which is impossible.
    have abne5 : ¬ (a = 5 ∧ b = 5) := by
      by_contra! hab
      obtain ⟨ha, hb⟩ := hab
      subst a b
      ring_nf at eq
      have hcsq : c ^ 2 = 27 := by omega
      have notsq : ¬ (IsSquare (27 : ℤ)) := by native_decide
      rw [← hcsq] at notsq
      rw [IsSquare] at notsq
      revert notsq
      simp only [not_exists, imp_false, not_forall, Decidable.not_not]
      use c
      ring_nf
--We now assume that a ≤ b.      
    by_cases h : a ≤ b
--In particular, from the above, b is at least 6.    
    · have lb' : 6 ≤ b := by omega
--From the equation and the assumption on a and b, we deduce that c ^ 2 - 23 ≤ (b ^ 2 - 23) ^ 2.      
      have diseq : c ^ 2 - 23 ≤ (b ^ 2 - 23) ^ 2 := by
        rw [← eq, pow_two (b ^ 2 - 23)]
        gcongr
--Now, b ^ 2 - 23 divides (c + b) * (c - b), since it is equal to (c ^ 2 - 23) - (b ^ 2 - 23).  
      have dvd : b ^ 2 - 23 ∣ (c + b) * (c - b) := by
        have bsqlecsq : b ^ 2 ≤ c ^ 2 := by
          have : b ^ 2 - 23 ∣ c ^ 2 - 23 := by
            use a ^ 2 - 23
            rw [← eq, mul_comm]
          apply Int.le_of_dvd at this
          all_goals omega
        have blec : b ≤ c := by
          rw [pow_le_pow_iff_left₀ (by omega) (by omega) (by omega : 2 ≠ 0)] at bsqlecsq
          exact bsqlecsq
        have : (c + b) * (c - b) = c ^ 2 - b ^ 2 := by
          ring_nf
        rw [this, (by omega : c ^ 2 - b ^ 2 = (c ^ 2 - 23) - (b ^ 2 - 23))]
        apply dvd_sub
        · use a ^ 2 - 23
          rw [← eq, mul_comm]
        · exact Int.dvd_refl (b ^ 2 - 23)
--Since b ^ 2 - 23 is prime, it divides either c + b or c - b.          
      rw [Prime.dvd_mul hb] at dvd
      rcases dvd with dvd | dvd
--In the first case, we have that in fact c + b = b ^ 2 - 23, since otherwise it would be at least 2 * (b ^ 2 - 23), which yields a contradiction.      
      · by_cases ne : b ^ 2 - 23 < c + b
        · have : 2 * (b ^ 2 - 23) ≤ c + b := by
            obtain ⟨r,hr⟩ := dvd
            have : 2 ≤ r := by
              by_contra! r1
              have : 0 < r := by
                have : 0 < (b ^ 2 - 23) * r := by omega
                rw [← pos_iff_pos_of_mul_pos this]
                omega
              interval_cases r
              omega
            rw [hr, mul_comm]
            gcongr
          have : c ≥ 2 * b ^ 2 - b - 46 := by omega
          have : 2 * b ^ 2 - b - 46 ≥ b ^ 2 + b * 6 - b - 46 := by
            rw [two_mul]
            gcongr
            rw [pow_two]
            gcongr
          have : b ^ 2 + b * 6 - b - 46 ≥ b ^ 2 + 5 * 6 - 46 := by
            gcongr
            have : b ^ 2 + b * 6 - b = b ^ 2 + (b * 6 - b) := by omega
            rw [this]
            gcongr
            omega
          have : c ≥ b ^ 2 - 16 := by omega
          have : b ^ 4 - 46 * b ^ 2 + 529 ≥ b ^ 4 - 32 * b^2 + 233 := by
            rw [(by ring_nf : b ^ 4 - 46 * b ^ 2 + 529 = (b ^ 2 - 23) ^ 2)]
            have : (b ^ 2 - 23) ^ 2 ≥ c ^ 2 - 23 := by omega
            apply le_trans _ this
            have : c ^ 2 - 23 ≥ (b ^ 2 - 16) ^ 2 - 23 := by
              gcongr
              omega
            apply le_trans _ this
            ring_nf
            apply le_of_eq
            rfl
          have : 296 ≥ 14 * b ^ 2 := by omega
          have : 14 * b ^ 2 ≥ 14 * 6^2 := by gcongr
          omega
--From the equalities obtained, we deduce the parities of a, b, and c. In particular, the prime number a ^ 2 - 23 is even, thus it is 2, so a = 5.          
        · have eq' : b ^ 2 - 23 = c + b := by
            obtain ⟨r,hr⟩ := dvd
            suffices r = 1 by
              rw [this, mul_one] at hr
              omega
            by_contra! r1
            have : 0 < r := by
              have : 0 < (b ^ 2 - 23) * r := by omega
              rw [← pos_iff_pos_of_mul_pos this]
              omega
            have : 1 < r := by omega
            rw [hr] at ne
            revert ne
            simp only [not_lt, imp_false, not_le]
            nth_rw 1 [← mul_one (b ^ 2 - 23)]
            gcongr
          have bodd : Odd (b ^ 2 - 23) := by
            have : b ^ 2 - 23 ≥ 13 := by
              simp_rw [le_sub_iff_add_le]
              ring_nf
              rw [(by omega : (36 : ℤ) = 6 ^ 2)]
              gcongr
            by_contra even
            rw [Int.not_odd_iff_even, even_iff_two_dvd] at even
            rw [Prime.dvd_prime_iff_associated (by simp; decide) hb] at even
            unfold Associated at even
            obtain ⟨u,hu⟩ := even
            have := Int.units_eq_one_or u
            rcases this with u1 | u1
            all_goals
              subst u1
              simp at hu
              omega
          have : Even b := by
            rw [Int.odd_sub'] at bodd
            have h23 : Odd 23 := by decide
            rw [Int.even_pow] at bodd
            simp at eq'
            tauto
          have : Odd c := by
            have : c = b ^ 2 - 23 - b := by omega
            rw [this, Int.odd_sub]
            tauto
          have : Even (c ^ 2 - 23) := by
            rw [Int.even_sub', Int.odd_pow]
            simp [this]
            decide
          have : Even (a ^ 2 - 23) := by
            rw [← eq] at this
            by_contra! aodd
            rw [Int.not_even_iff_odd] at aodd
            apply Odd.mul at aodd
            specialize aodd bodd
            rw [← Int.not_even_iff_odd] at aodd
            contradiction
          have : a ^ 2 - 23 = 2 := by
            rw [even_iff_two_dvd] at this
            rw [Prime.dvd_prime_iff_associated (by simp; decide) ha] at this
            unfold Associated at this
            obtain ⟨u,hu⟩ := this
            have := Int.units_eq_one_or u
            rcases this with u1 | u1
            all_goals
              subst u1
              simp at hu
              omega
          have : a = 5 := by
            have : a ^ 2 = 5 ^ 2 := by omega
            rw [sq_eq_sq₀ (by omega) (by omega)] at this
            exact this
--From the equality (c + b) * (c - b) = (c ^ 2 - 23) - (b ^ 2 - 23) = (a ^ 2 - 24) * (b ^ 2 - 23), and the fact that c + b = b ^ 2 - 23, we find that c - b = a ^ 2 - 24 = 1.
          have : (c + b) * (c - b) = (c ^ 2 - 23) - (b ^ 2 - 23) := by ring_nf
          rw [← eq] at this
          nth_rw 2 [← one_mul (b ^ 2 - 23)] at this
          rw [← sub_mul, eq', mul_comm] at this
          simp only [mul_eq_mul_right_iff] at this
          rcases this with eq'' | eq''
          · subst a
            have : c = b + 1 := by omega
            rw [this] at eq'
            have : (b + 4) * (b - 6) = 0 := by
              ring_nf
              omega
            rw [mul_eq_zero] at this
            rcases this with eq''' | eq'''
            · omega
            · have : b = 6 := by omega
              rw [this] at eq'
              have : c = 7 := by omega
              subst b c
              simp
          · omega
--If instead we assume that (b ^ 2 - 23) divides c - b, we find a contradiction.            
      · exfalso
        apply Int.le_of_dvd at dvd
        · have : (b ^ 2 - 23) ^ 2 < (c + b) * (c - b) := by
            rw [pow_two]
            apply mul_lt_mul
            all_goals omega
          have : (c + b) * (c - b) = (c ^ 2 - 23) - (b ^ 2 - 23) := by
            ring_nf
          have : (c ^ 2 - 23) - (b ^ 2 - 23) ≤ (b ^ 2 - 23) ^ 2 := by
            apply le_trans _ diseq
            nth_rw 2 [← sub_zero (c ^ 2 - 23)]
            rw [sub_le_sub_iff_left]
            omega
          omega
        · have : b ^ 2 - 23 ∣ c ^ 2 - 23 := by use a ^ 2 - 23; rw [← eq, mul_comm]
          apply Int.le_of_dvd at this
          simp at this
          rw [pow_le_pow_iff_left₀ (by omega) (by omega) (by omega : 2 ≠ 0)] at this
          rw [le_iff_lt_or_eq] at this
          rcases this with h' | h'
          · omega
          · rw [h'] at eq
            rw [← sub_eq_zero] at eq
            nth_rw 2 [← one_mul (c ^ 2 - 23)] at eq
            rw [← sub_mul] at eq
            simp at eq
            rcases eq with eq | eq
            · exfalso
              have : a ^ 2 = 24 := by omega
              have notsq : ¬ (IsSquare (24 : ℤ)) := by native_decide
              rw [← this] at notsq
              rw [IsSquare] at notsq
              revert notsq
              simp only [not_exists, imp_false, not_forall, Decidable.not_not]
              use a
              ring_nf
            · omega
          omega
--We repeat the proof in the case b < a.
    · have lb' : 6 ≤ a := by omega
      have diseq : c ^ 2 - 23 ≤ (a ^ 2 - 23) ^ 2 := by
        rw [← eq, pow_two (a ^ 2 - 23)]
        gcongr
        omega
      have dvd : a ^ 2 - 23 ∣ (c + a) * (c - a) := by
        have asqlecsq : a ^ 2 ≤ c ^ 2 := by
          have : a ^ 2 - 23 ∣ c ^ 2 - 23 := by
            use b ^ 2 - 23
            rw [← eq, mul_comm]
          apply Int.le_of_dvd at this
          all_goals omega
        have alec : a ≤ c := by
          rw [pow_le_pow_iff_left₀ (by omega) (by omega) (by omega : 2 ≠ 0)] at asqlecsq
          exact asqlecsq
        have : (c + a) * (c - a) = c ^ 2 - a ^ 2 := by
          ring_nf
        rw [this, (by omega : c ^ 2 - a ^ 2 = (c ^ 2 - 23) - (a ^ 2 - 23))]
        apply dvd_sub
        · use b ^ 2 - 23
          rw [← eq, mul_comm]
        · exact Int.dvd_refl (a ^ 2 - 23)
      rw [Prime.dvd_mul ha] at dvd
      rcases dvd with dvd | dvd
      · by_cases ne : a ^ 2 - 23 < c + a
        · have : 2 * (a ^ 2 - 23) ≤ c + a := by
            obtain ⟨r,hr⟩ := dvd
            have : 2 ≤ r := by
              by_contra! r1
              have : 0 < r := by
                have : 0 < (a ^ 2 - 23) * r := by omega
                rw [← pos_iff_pos_of_mul_pos this]
                omega
              interval_cases r
              omega
            rw [hr, mul_comm]
            gcongr
          have : c ≥ 2 * a ^ 2 - a - 46 := by omega
          have : 2 * a ^ 2 - a - 46 ≥ a ^ 2 + a * 6 - a - 46 := by
            rw [two_mul]
            gcongr
            rw [pow_two]
            gcongr
          have : a ^ 2 + a * 6 - a - 46 ≥ a ^ 2 + 5 * 6 - 46 := by
            gcongr
            have : a ^ 2 + a * 6 - a = a ^ 2 + (a * 6 - a) := by omega
            rw [this]
            gcongr
            omega
          have : c ≥ a ^ 2 - 16 := by omega
          have : a ^ 4 - 46 * a ^ 2 + 529 ≥ a ^ 4 - 32 * a ^ 2 + 233 := by
            rw [(by ring_nf : a ^ 4 - 46 * a ^ 2 + 529 = (a ^ 2 - 23) ^ 2)]
            have : (a ^ 2 - 23) ^ 2 ≥ c ^ 2 - 23 := by omega
            apply le_trans _ this
            have : c ^ 2 - 23 ≥ (a ^ 2 - 16) ^ 2 - 23 := by
              gcongr
              omega
            apply le_trans _ this
            ring_nf
            apply le_of_eq
            rfl
          have : 296 ≥ 14 * a ^ 2 := by omega
          have : 14 * a ^ 2 ≥ 14 * 6^2 := by gcongr
          omega
        · have eq' : a ^ 2 - 23 = c + a := by
            obtain ⟨r,hr⟩ := dvd
            suffices r = 1 by
              rw [this, mul_one] at hr
              omega
            by_contra! r1
            have : 0 < r := by
              have : 0 < (a ^ 2 - 23) * r := by omega
              rw [← pos_iff_pos_of_mul_pos this]
              omega
            have : 1 < r := by omega
            rw [hr] at ne
            revert ne
            simp only [not_lt, imp_false, not_le]
            nth_rw 1 [← mul_one (a ^ 2 - 23)]
            gcongr
          have aodd : Odd (a ^ 2 - 23) := by
            have : a ^ 2 - 23 ≥ 13 := by
              simp_rw [le_sub_iff_add_le]
              ring_nf
              rw [(by omega : (36 : ℤ) = 6 ^ 2)]
              gcongr
            by_contra even
            rw [Int.not_odd_iff_even, even_iff_two_dvd] at even
            rw [Prime.dvd_prime_iff_associated (by simp; decide) ha] at even
            unfold Associated at even
            obtain ⟨u,hu⟩ := even
            have := Int.units_eq_one_or u
            rcases this with u1 | u1
            all_goals
              subst u1
              simp at hu
              omega
          have : Even a := by
            rw [Int.odd_sub'] at aodd
            have h23 : Odd 23 := by decide
            rw [Int.even_pow] at aodd
            simp at eq'
            tauto
          have : Odd c := by
            have : c = a ^ 2 - 23 - a := by omega
            rw [this, Int.odd_sub]
            tauto
          have : Even (c ^ 2 - 23) := by
            rw [Int.even_sub', Int.odd_pow]
            simp [this]
            decide
          have : Even (b ^ 2 - 23) := by
            rw [← eq] at this
            by_contra! bodd
            rw [Int.not_even_iff_odd] at bodd
            apply Odd.mul at bodd
            specialize bodd aodd
            rw [← Int.not_even_iff_odd, mul_comm] at bodd
            contradiction
          have : b ^ 2 - 23 = 2 := by
            rw [even_iff_two_dvd] at this
            rw [Prime.dvd_prime_iff_associated (by simp; decide) hb] at this
            unfold Associated at this
            obtain ⟨u,hu⟩ := this
            have := Int.units_eq_one_or u
            rcases this with u1 | u1
            all_goals
              subst u1
              simp at hu
              omega
          have : b = 5 := by
            have : b ^ 2 = 5 ^ 2 := by omega
            rw [sq_eq_sq₀ (by omega) (by omega)] at this
            exact this
          have : (c + a) * (c - a) = (c ^ 2 - 23) - (a ^ 2 - 23) := by ring_nf
          rw [← eq] at this
          nth_rw 2 [← mul_one (a ^ 2 - 23)] at this
          rw [← mul_sub, eq'] at this
          simp only [mul_eq_mul_left_iff] at this
          rcases this with eq'' | eq''
          · subst b
            have : c = a + 1 := by omega
            rw [this] at eq'
            have : (a + 4) * (a - 6) = 0 := by
              ring_nf
              omega
            rw [mul_eq_zero] at this
            rcases this with eq''' | eq'''
            · omega
            · have : a = 6 := by omega
              rw [this] at eq'
              have : c = 7 := by omega
              subst a c
              simp
          · omega
      · exfalso
        apply Int.le_of_dvd at dvd
        · have : (a ^ 2 - 23) ^ 2 < (c + a) * (c - a) := by
            rw [pow_two]
            apply mul_lt_mul
            all_goals omega
          have : (c + a) * (c - a) = (c ^ 2 - 23) - (a ^ 2 - 23) := by
            ring_nf
          have : (c ^ 2 - 23) - (a ^ 2 - 23) ≤ (a ^ 2 - 23) ^ 2 := by
            apply le_trans _ diseq
            nth_rw 2 [← sub_zero (c ^ 2 - 23)]
            rw [sub_le_sub_iff_left]
            omega
          omega
        · have : a ^ 2 - 23 ∣ c ^ 2 - 23 := by use b ^ 2 - 23; rw [← eq, mul_comm]
          apply Int.le_of_dvd at this
          simp at this
          rw [pow_le_pow_iff_left₀ (by omega) (by omega) (by omega : 2 ≠ 0)] at this
          rw [le_iff_lt_or_eq] at this
          rcases this with h' | h'
          · omega
          · rw [h'] at eq
            rw [← sub_eq_zero] at eq
            nth_rw 2 [← mul_one (c ^ 2 - 23)] at eq
            rw [← mul_sub] at eq
            simp at eq
            rcases eq with eq | eq
            · omega
            · exfalso
              have : b ^ 2 = 24 := by omega
              have notsq : ¬ (IsSquare (24 : ℤ)) := by native_decide
              rw [← this] at notsq
              rw [IsSquare] at notsq
              revert notsq
              simp only [not_exists, imp_false, not_forall, Decidable.not_not]
              use b
              ring_nf
          omega
--To conclude, we check that, conversely, the solutions proposed work.
  · intro h
    rcases h with ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩
    all_goals subst ha hb hc
    constructor
    · rw [(by omega : (5 : ℤ) ^ 2 - 23 = 2)]
      simp only [Int.prime_ofNat_iff]
      decide
    · constructor
      · rw [(by omega : (6 : ℤ) ^ 2 - 23 = 13)]
        simp only [Int.prime_ofNat_iff]
        decide
      · ring_nf
    constructor
    · rw [(by omega : (6 : ℤ) ^ 2 - 23 = 13)]
      simp only [Int.prime_ofNat_iff]
      decide
    · constructor
      · rw [(by omega : (5 : ℤ) ^ 2 - 23 = 2)]
        simp only [Int.prime_ofNat_iff]
        decide
      · ring_nf