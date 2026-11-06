import Mathlib


/- Find all pairs of positive integers $(a, b)$ such that $a^{2} b \mid\left(b^{2}+3 a\right)$ $\square$ -/
theorem number_theory_204400 (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (h : a ^ 2 * b ∣ (b ^ 2 + 3 * a)) : (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 3) := by
--From the divisibility condition we obtain an equation in a b and k, where is the quotient.
  obtain ⟨k, hk⟩ := h
--Let d be the gcd of a and b. We rewrite a as a = d * a1 and b as b = d * b1, where a1 and b1 are coprime integers.
  set d := a.gcd b with hd
  have dpos : 0 < d := by
    rw [Int.gcd_pos_iff]
    omega
  have : (d : ℤ) ∣ a := by exact Int.gcd_dvd_left
  obtain ⟨a1,ha1⟩ := this
  have : (d : ℤ) ∣ b := by exact Int.gcd_dvd_right
  obtain ⟨b1,hb1⟩ := this
  have coprime : a1.gcd b1 = 1 := by
    have ha1' : a1 = a / d := by rw [ha1]; refine Int.eq_ediv_of_mul_eq_right (by omega) rfl
    have hb1' : b1 = b / d := by rw [hb1]; refine Int.eq_ediv_of_mul_eq_right (by omega) rfl
    rw [ha1', hb1', hd, Int.gcd_div_gcd_div_gcd dpos]
  have : 0 < a1 := by
    rw [ha1] at ha
    zify at dpos
    rw [pos_iff_pos_of_mul_pos ha] at dpos
    omega
  have : 0 < b1 := by
    rw [hb1] at hb
    zify at dpos
    rw [pos_iff_pos_of_mul_pos hb] at dpos
    omega
--We rewrite and simplify the equation in terms of a1 and b1.
  rw [ha1, hb1] at hk
  ring_nf at hk
  rw [pow_two, pow_three, ← sub_eq_zero, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, ← mul_add, ← mul_sub] at hk
  simp only [mul_eq_zero, Nat.cast_eq_zero] at hk
  rcases hk with d0 | hk
  · omega
--We prove that d divides a1*3 and a1 divides d*b1^2 (hence d, since a1 and b1 are coprime).
  · have d_dvd : (d : ℤ) ∣ a1 * 3 := by
      use (- b1 ^ 2 + d * b1 * a1 ^ 2 * k)
      ring_nf
      linarith
    have a1_dvd : a1 ∣ d * b1 ^ 2 := by
      use (d * d * b1 * a1 * k - 3)
      ring_nf
      linarith
    apply IsCoprime.dvd_of_dvd_mul_right at a1_dvd
    swap
    rw [← pow_one a1]
    apply IsCoprime.pow
    rw [← Int.gcd_eq_one_iff_coprime]
    exact coprime
--We obtain n and m from these divisibility conditions.
    obtain ⟨m,hm⟩ := d_dvd
    obtain ⟨n,hn⟩ := a1_dvd
    rw [hn, mul_assoc] at hm
    simp only [mul_eq_mul_left_iff] at hm
--We obtain that m*n=3 (since a1=0 is impossible).
    rcases hm with h3 | a1_0
--Since m*n=3, one of them is 1 and the other is 3.
    · have : (n = 3 ∧ m = 1) ∨ (n = 1 ∧ m = 3) := by
        have : 0 < n := by
          zify at dpos
          rw [hn] at dpos
          rw [← pos_iff_pos_of_mul_pos dpos]
          rw [ha1] at ha
          rw [← pos_iff_pos_of_mul_pos ha]
          omega
        have : 0 < m := by
          have : (0 : ℤ) < 3 := by omega
          rw [h3] at this
          rw [← pos_iff_pos_of_mul_pos this]
          omega
        have := dvd_of_eq h3
        rw [Prime.dvd_mul (by simp; decide)] at this
        rcases this with h3n | h3m
        · left
          have : n ∣ 3 := by use m
          have : n = 3 := by
            apply Int.dvd_antisymm
            · omega
            · omega
            · exact this
            · exact h3n
          subst n
          nth_rw 1 [← mul_one 3] at h3
          simp only [mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, left_eq_mul₀] at h3
          omega
        · right
          have : m ∣ 3 := by use n; rw [mul_comm]; exact h3
          have : m = 3 := by
            apply Int.dvd_antisymm
            · omega
            · omega
            · exact this
            · exact h3m
          subst m
          nth_rw 1 [← one_mul 3] at h3
          simp only [one_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, right_eq_mul₀] at h3
          omega
--We have two cases: n=3 and m=1, or n=1 and m=3.
      rcases this with ⟨hn,hm⟩ | ⟨hn,hm⟩
--If n=3, we have d=3*a1, and we replace it in the equation. Simplifying, we find that b1=1.
      · subst n
        rw [hn] at hk
        nth_rw 1 [← mul_one (a1 * 3)] at hk
        rw [← mul_add, ← mul_sub] at hk
        simp only [mul_eq_zero, OfNat.ofNat_ne_zero, or_false] at hk
        rcases hk with a1_0 | hk
        · omega
        · have : b1 ∣ 1 := by
            use (- b1 + a1 * 3 * a1 ^ 2 * k)
            ring_nf
            linarith
          have : b1 = 1 := by
            apply Int.dvd_antisymm
            · rw [hb1] at hb
              zify at dpos
              rw [pos_iff_pos_of_mul_pos hb] at dpos
              omega
            · omega
            · exact this
            · use b1
              ring_nf
          rw [this] at hk
          ring_nf at hk
--We subsitute b1=1 in the equation, and we find that 3 * a1^3 * k=2. In particular, 3 divides 2, a contradiction.
          have : (3 : ℤ) ∣ 2 := by
            use a1 ^ 3 * k
            omega
          contradiction
--We now consider the case n=1 and m=3.
      · subst n
        rw [mul_one] at hn
        rw [hn, ← mul_add, ← mul_sub] at hk
        simp only [mul_eq_zero] at hk
--Replacing d=a1 * 1 in the equation and simplifying, we find that b1=3.
        rcases hk with a1_0 | hk
        · omega
--We have that either b1=3 or b1=1.
        · have : b1 ∣ 3 := by
            use (- b1 + a1 *  a1 ^ 2 * k)
            ring_nf
            linarith
          obtain ⟨r,hr⟩ := this
          have := dvd_of_eq hr
          rw [Prime.dvd_mul (by simp; decide)] at this
          rcases this with h3b1 | h3r
          · have : b1 = 3 := by
              apply Int.dvd_antisymm
              · omega
              · omega
              · use r
              · exact h3b1
--We replace b1=3 in the equation. We obtain k*a1^3=4.
            rw [this] at hk
            ring_nf at hk
            rw [(by omega : (12 : ℤ) = 4 * 3), ← sub_mul] at hk
            simp only [mul_eq_zero, OfNat.ofNat_ne_zero, or_false] at hk
            have new_eq : a1 ^ 3 * k = 4 := by omega
--We consider the 2-adic valuations of both sides, and find that 4 divides k.
            have padic_eq : padicValInt 2 (a1 ^ 3 * k) = padicValInt 2 4 := by rw [new_eq]
            have : 0 < k := by
              have : (0 : ℤ) < 4 := by omega
              rw [← new_eq] at this
              rw [← pos_iff_pos_of_mul_pos this]
              apply Lean.Omega.Int.pos_pow_of_pos a1 3
              omega
            rw [padicValInt.mul (by simp; omega) (by omega), pow_three, padicValInt.mul (by omega) (by simp; omega), padicValInt.mul (by omega) (by omega)] at padic_eq
            ring_nf at padic_eq
            have : padicValInt 2 4 = 2 := by native_decide
            rw [this] at padic_eq
            have : padicValInt 2 a1 = 0 := by
              by_contra! pos
              have : 0 < padicValInt 2 a1 := by
                rw [lt_iff_le_and_ne]
                simp only [zero_le, true_and]
                exact pos.symm
              have : padicValInt 2 a1 * 3 + padicValInt 2 k ≥ 3 := by omega
              rw [padic_eq] at this
              omega
            rw [this, zero_mul, zero_add] at padic_eq
            have : 4 ∣ k := by
              let p := 2
              have : Fact (Nat.Prime p) := by decide
              rw [(by simp : (4 : ℤ) = p ^ 2), padicValInt_dvd_iff 2 k]
              right
              rw [padic_eq]
--Therefore, k=4 and a1=1.
            obtain ⟨k',hk'⟩ := this
            rw [hk', mul_comm, ← sub_eq_zero, mul_assoc] at new_eq
            nth_rw 2 [← mul_one 4] at new_eq
            rw [← mul_sub] at new_eq
            simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at new_eq
            have : a1 ∣ 1 := by
              use k' * a1 ^ 2
              ring_nf
              rw [mul_comm]
              omega
            have : a1 = 1 := by
              apply Int.dvd_antisymm
              · omega
              · omega
              · exact this
              · use a1; ring_nf
--From all this, we find the solution a=1 and b=3.
            subst a1
            rw [this] at ha1 hb1
            ring_nf at ha1 hb1
            subst b1
            right
            omega
--We are now in the case b1=1. We obtain the same equation a1^3*k=4 and find again that k=4 and a1=1.
          · obtain ⟨r',hr'⟩ := h3r
            rw [hr', mul_comm, ← sub_eq_zero, mul_assoc] at hr
            nth_rw 1 [← mul_one 3] at hr
            rw [← mul_sub] at hr
            simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hr
            have : b1 ∣ 1 := by use r'; rw [mul_comm]; omega
            have : b1 = 1 := by
              apply Int.dvd_antisymm
              all_goals omega
            subst b1
            ring_nf at hk
            have new_eq : a1 ^ 3 * k = 4 := by omega
            have padic_eq : padicValInt 2 (a1 ^ 3 * k) = padicValInt 2 4 := by rw [new_eq]
            have : 0 < k := by
              have : (0 : ℤ) < 4 := by omega
              rw [← new_eq] at this
              rw [← pos_iff_pos_of_mul_pos this]
              apply Lean.Omega.Int.pos_pow_of_pos a1 3
              omega
            rw [padicValInt.mul (by simp; omega) (by omega), pow_three, padicValInt.mul (by omega) (by simp; omega), padicValInt.mul (by omega) (by omega)] at padic_eq
            ring_nf at padic_eq
            have : padicValInt 2 4 = 2 := by native_decide
            rw [this] at padic_eq
            have : padicValInt 2 a1 = 0 := by
              by_contra! pos
              have : 0 < padicValInt 2 a1 := by
                rw [lt_iff_le_and_ne]
                simp only [zero_le, true_and]
                exact pos.symm
              have : padicValInt 2 a1 * 3 + padicValInt 2 k ≥ 3 := by omega
              rw [padic_eq] at this
              omega
            rw [this, zero_mul, zero_add] at padic_eq
            have : 4 ∣ k := by
              let p := 2
              have : Fact (Nat.Prime p) := by decide
              rw [(by simp : (4 : ℤ) = p ^ 2), padicValInt_dvd_iff 2 k]
              right
              rw [padic_eq]
            obtain ⟨k',hk'⟩ := this
            rw [hk', mul_comm, ← sub_eq_zero, mul_assoc] at new_eq
            nth_rw 2 [← mul_one 4] at new_eq
            rw [← mul_sub] at new_eq
            simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at new_eq
            have : a1 ∣ 1 := by
              use k' * a1 ^ 2
              ring_nf
              rw [mul_comm]
              omega
            have : a1 = 1 := by
              apply Int.dvd_antisymm
              · omega
              · omega
              · exact this
              · use a1; ring_nf
--From all this, we find the solution a=1 and b=1.
            subst a1
            rw [this] at ha1 hb1
            ring_nf at ha1 hb1
            subst b
            left
            omega
--We are left with the case a1=0, which is impossible.
    · omega