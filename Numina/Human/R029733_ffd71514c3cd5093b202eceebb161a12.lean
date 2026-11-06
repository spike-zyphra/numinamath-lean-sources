import Mathlib

/- Exercise 3. Determine all natural integers $x, y$ and $z$ such that


$$

45^{x}-6^{y}=2019^{z}

$$
 -/
theorem number_theory_290854 (x y z : ℕ) :
    (45 : ℤ) ^ x - 6 ^ y = 2019 ^ z ↔ (x, y, z) = (2, 1, 1) := by
    --First, we rewrite the equation by factoring 45, 6 and 2019.
    rw [(by norm_num : (45 : ℤ) = 3^2 * 5), (by norm_num : (6 : ℤ) = 2 * 3), (by norm_num : (2019 : ℤ) = 3 * 673), mul_pow, ← pow_mul, mul_pow, mul_pow]
    --We will need the "fact" that 5 is prime several times.
    have Prime5 : Fact (Nat.Prime 5) := by
      decide
    constructor
    --We will prove the forward direction first.
    · intro eq
    --We divide the proof in three cases: y > 2x, y = 2x and y < 2x.
      by_cases h : y > 2 * x
    --When y > 2x, we can divide the equation by 3^(2x). First we have this useful lemma that 3^y can be written as 3^(2x) * 3^(y - 2x).
      · have h3y : (3 : ℤ) ^ y = 3 ^ (2 * x) * 3 ^ (y - 2 * x) := by
          rw [← pow_add, (by omega : 2 * x + (y - 2 * x) = y)]
        have : (3 : ℤ) ^ (2 * x) ∣ 3 ^ z * 673 ^ z := by
          rw [← eq]
          use 5 ^ x - 2 ^ y * 3 ^ (y - 2 * x)
          ring_nf
          rw [mul_assoc, ← pow_add, (by omega : x * 2 + (y - x * 2) = y)]
    --Now, exploiting the fact that 3^(2x) divides all terms in the equation, we will arrive at 2x=z.
        have : 2 * x = z := by
          apply Prime.pow_dvd_of_dvd_mul_right at this
          · have : 3 ^ (2 * x) ∣ 3 ^ z := by exact_mod_cast this
            rw [Nat.pow_dvd_pow_iff_le_right (by omega)] at this
            rw [le_iff_lt_or_eq] at this
            rcases this with hlt | heq
            · rw [lt_iff_exists_add] at hlt
              obtain ⟨k, hk⟩ := hlt
              nth_rw 1 [hk.2] at eq
              rw [pow_add, h3y, mul_comm (2 ^ y), mul_assoc, ← mul_sub, mul_assoc] at eq
              simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, mul_eq_zero, false_or, false_and, or_false] at eq
              have eq' : (5 : ℤ) ^ x = 3 ^ (y - 2 * x) * 2 ^ y + 3 ^ k * 673 ^ z := by rw [← eq]; ring_nf
              have : (3 : ℤ) ∣ 5 ^ x := by
                rw [eq']
                apply Dvd.dvd.add
                · rw [Prime.dvd_mul (by simp; decide)]
                  left
                  rw [Prime.dvd_pow_iff_dvd (by simp; decide)]
                  omega
                · rw [Prime.dvd_mul (by simp; decide)]
                  left
                  rw [Prime.dvd_pow_iff_dvd (by simp; decide)]
                  omega
              by_cases h0 : x = 0
              · rw [h0, pow_zero] at this
                contradiction
              · rw [Prime.dvd_pow_iff_dvd (by simp; decide)] at this
                contradiction
                omega
            · exact heq
          · simp; decide
          · intro dvd
            apply Prime.dvd_of_dvd_pow at dvd
            · contradiction
            · simp; decide
        --We write 2x in place of z in the equation and simplify.
        rw [← this, h3y, mul_comm (2^y), mul_assoc, ← mul_sub] at eq
        simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, mul_eq_zero, false_or, false_and, or_false] at eq
        --We have that a number smaller than 5^x is equal to 673^(2x), which is impossible.
        have : (5 : ℤ) ^ x - 3 ^ (y - 2 * x) * 2 ^ y < 5 ^ x := by
          simp only [sub_lt_self_iff, Nat.ofNat_pos, pow_pos, mul_pos_iff_of_pos_left]
        rw [eq, pow_mul] at this
        norm_num at this
        have : 452929 ^ x < 5 ^ x := by exact_mod_cast this
        apply lt_of_pow_lt_pow_left' at this
        omega
      --Now we will consider the case y = 2x.
      · by_cases h : y = 2 * x
      -- Replacing y by 2x in the equation, we prove first of all that 2x ≤ z.
        · rw [h, mul_comm (2 ^ (2 * x)), ← mul_sub] at eq
          have dvd : (3 : ℤ) ^ (2 * x) ∣ 3 ^ z * 673 ^ z := by
            use (5 ^ x - 2 ^ (2 * x))
            rw [eq]
          have : IsCoprime ((3 : ℤ) ^ (2 * x)) (673 ^ z) := by
            have := Nat.coprime_pow_primes (2 * x) z (by decide : Nat.Prime 3) (by native_decide : Nat.Prime 673) (by omega : 3 ≠ 673)
            rw [← Nat.isCoprime_iff_coprime] at this
            exact_mod_cast this
          apply IsCoprime.dvd_of_dvd_mul_right this at dvd
          have : 2 * x ≤ z := by
            rw_mod_cast [Nat.pow_dvd_pow_iff_le_right (by omega)] at dvd
            exact dvd
          --Once again, we obtain an equality between two terms that are one smaller than the other, so we get a contradiction.
          rw [le_iff_exists_add] at this
          obtain ⟨k, hk⟩ := this
          nth_rw 1 [hk] at eq
          rw [pow_add, mul_assoc] at eq
          simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, mul_eq_mul_left_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, mul_eq_zero, false_or, false_and, or_false] at eq
          have rhs : (3 : ℤ) ^ k * 673 ^ z ≥ 673 ^ z := by
            simp only [ge_iff_le, Nat.ofNat_pos, pow_pos, le_mul_iff_one_le_left]
            rw_mod_cast [Nat.one_le_iff_ne_zero]
            simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true]
          have med : (5 : ℤ) ^ z ≤ 673 ^ z := by
            gcongr
            omega
          have lhs : (5 : ℤ) ^ x - 2 ^ (2 * x) < 5 ^ z := by
            apply lt_of_lt_of_le
            · have : (5 : ℤ) ^ x - 2 ^ (2 * x) < 5 ^ x := by simp
              exact this
            · gcongr
              omega
              linarith
          have : (5 : ℤ) ^ x - 2 ^ (2 * x) < 3 ^ k * 673 ^ z := by
            apply lt_of_lt_of_le lhs
            apply le_trans med
            exact rhs
          rw [← eq] at this
          omega
        --Finally, we consider the case where y<2x.
        · have h : y < 2 * x := by simp only [gt_iff_lt, not_lt] at h; omega
          rw [(by omega : 2 * x = y + (2 * x - y)), pow_add, mul_comm (2 ^ y), mul_assoc, ← mul_sub] at eq
        --We prove that y=z, by exploiting the fact that 3^y divides exactly the right-hand side of the equation and 3^z divides exactly the left-hand side.
          have yeqz : y = z := by
            apply le_antisymm
            · rw [← Nat.pow_dvd_pow_iff_le_right (by omega : 1 < 3)]
              have dvd : (3 : ℤ) ^ y ∣ 3 ^ z * 673 ^ z := by
                use (3 ^ (2 * x - y) * 5 ^ x - 2 ^ y)
                rw [eq]
              have := Nat.coprime_pow_primes y z (by decide : Nat.Prime 3) (by native_decide : Nat.Prime 673) (by omega : 3 ≠ 673)
              apply IsCoprime.dvd_of_dvd_mul_right at dvd
              · exact_mod_cast dvd
              · rw [← Nat.isCoprime_iff_coprime] at this
                exact_mod_cast this
            · rw [← Nat.pow_dvd_pow_iff_le_right (by omega : 1 < 3)]
              have dvd : (3 : ℤ) ^ z ∣ 3 ^ y * (3 ^ (2 * x - y) * 5 ^ x - 2 ^ y) := by
                use 673 ^ z
              apply IsCoprime.dvd_of_dvd_mul_right at dvd
              · exact_mod_cast dvd
              · rw [← pow_one (3 ^ (2 * x - y) * 5 ^ x - 2 ^ y)]
                apply IsCoprime.pow
                have : (3 : ℤ) ^ (2 * x - y) = 3 * (3 ^ (2 * x - y - 1)) := by
                  nth_rw 2 [← pow_one 3]
                  rw [← pow_add, (by omega : 1 + (2 * x - y - 1) = 2 * x - y)]
                rw [this, mul_assoc, sub_eq_add_neg]
                apply IsCoprime.mul_add_left_right
                rw [← pow_one 3]
                apply IsCoprime.neg_right
                apply IsCoprime.pow
                norm_num
        --We can now replace y with z in the equation and simplify it.
          subst yeqz
          simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, or_false] at eq
        --We consider separately the cases where y=0, y=1 and y≥2.
          by_cases h : y = 0
        --If y=0, we have that 2 is equal to a power of 3 times a power of 5, which is impossible.
          · subst h
            ring_nf at eq
            rw [tsub_zero] at eq
            have : (3 : ℤ) ^ (x * 2) * 5 ^ x = 2 := by linarith
            have : (3 : ℤ) ∣ 2 := by
              use (3 ^ (x * 2 - 1) * 5 ^ x)
              rw [← this]
              nth_rw 2 [← pow_one 3]
              rw [← mul_assoc, ← pow_add, (by omega : 1 + (x * 2 - 1) = x * 2)]
            contradiction
          --If y=1, we find the only solution to the equation, that is x = 2, y = 1 and z = 1.
          · by_cases h : y = 1
            · subst h
              ring_nf at eq
              have : (3 : ℤ) ^ (x * 2 - 1) * 5 ^ x = 675 := by linarith
              rw [(by omega : (675 : ℤ) = 3 ^ 3 * 5 ^ 2)] at this
              have : 3 ^ (x * 2 - 1) * 5 ^ x = 3 ^ 3 * 5 ^ 2 := by exact_mod_cast this
              have padic := congr_arg (padicValNat 5) this
              have val : padicValNat 5 (3 ^ 3 * 5 ^ 2) = 2 := by
                native_decide
              rw [val] at padic
              rw [padicValNat.mul (by positivity) (by positivity)] at padic
              rw [padicValNat.prime_pow] at padic
              have : padicValNat 5 (3 ^ (x * 2 - 1)) = 0 := by
                apply padicValNat.eq_zero_of_not_dvd
                intro hdvd
                apply Nat.Prime.dvd_of_dvd_pow (by decide) at hdvd
                contradiction
              rw [this] at padic
              norm_num at padic
              subst padic
              rfl
          --If y ≥ 2, we look at the equation modulo 5 and 4.
            · have h : y ≥ 2 := by simp only [gt_iff_lt, not_lt, ge_iff_le] at h; omega
              have evenoddy := Nat.even_or_odd' y
              obtain ⟨c,hc⟩ := evenoddy
              rcases hc with hc | hc
          --The equation modulo 5 gives us a contradiction if y is even.
              · have : x ≥ 1 := by omega
                have mod5 : (5 : ℤ) ∣ 673 ^ y + 2 ^ y - 3 ^ (x * 2 - y) * 5 ^ x := by
                  rw [← eq]
                  ring_nf
                  simp only [dvd_zero]
                rw [dvd_sub_left (by use 3 ^ (x * 2 - y) * 5 ^ (x - 1); ring_nf; nth_rw 3 [← pow_one 5]; rw [mul_assoc, ← pow_add, (by omega : x - 1 + 1 = x)])] at mod5
                rw_mod_cast [← Nat.modEq_zero_iff_dvd] at mod5
                rw [← ZMod.eq_iff_modEq_nat] at mod5
                simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero] at mod5
                have : 673 ≡ 3 [MOD 5] := by
                  decide
                rw [← ZMod.eq_iff_modEq_nat] at this
                simp only [Nat.cast_ofNat] at this
                rw [this] at mod5
                rw [hc, pow_mul, pow_mul] at mod5
                norm_num at mod5
                have : 9 ≡ 4 [MOD 5] := by
                  decide
                rw [← ZMod.eq_iff_modEq_nat] at this
                simp only [Nat.cast_ofNat] at this
                rw [this] at mod5
                ring_nf at mod5
                rw [mul_eq_zero] at mod5
                rcases mod5 with mod5 | mod5
                · simp only [pow_eq_zero_iff', ne_eq] at mod5
                  have : 4 ≡ 0 [MOD 5] := by
                    rw [← ZMod.eq_iff_modEq_nat]
                    exact_mod_cast mod5.1
                  contradiction
                · have : 2 ≡ 0 [MOD 5] := by
                    rw [← ZMod.eq_iff_modEq_nat]
                    exact_mod_cast mod5
                  contradiction
          --The equation modulo 4 gives us a contradiction if y is odd.
              · rw [ge_iff_le, le_iff_exists_add] at h
                obtain ⟨k, hk⟩ := h
                subst hk
                ring_nf at eq
                have mod4 : (4 : ℤ) ∣ -(2 ^ k * 4) + 3 ^ (x * 2 - (2 + k)) * 5 ^ x - 673 ^ k * 452929 := by
                  rw [← sub_eq_zero] at eq
                  rw [eq]
                  simp only [dvd_zero]
                rw [add_sub_assoc, dvd_add_right (by use (- 2 ^ k); ring_nf)] at mod4
                have mod4 : 673 ^ k * 452929 ≡ 3 ^ (x * 2 - (2 + k)) * 5 ^ x [MOD 4] := by
                  rw [Nat.modEq_iff_dvd]
                  exact_mod_cast mod4
                rw [← ZMod.eq_iff_modEq_nat] at mod4
                simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at mod4
                have : 673 ≡ 1 [MOD 4] := by
                  decide
                rw [← ZMod.eq_iff_modEq_nat] at this
                simp only [Nat.cast_ofNat] at this
                rw [this] at mod4
                have : 452929 ≡ 1 [MOD 4] := by
                  decide
                rw [← ZMod.eq_iff_modEq_nat] at this
                simp only [Nat.cast_ofNat] at this
                rw [this] at mod4
                ring_nf at mod4
                have : 5 ≡ 1 [MOD 4] := by
                  decide
                rw [← ZMod.eq_iff_modEq_nat] at this
                simp only [Nat.cast_ofNat] at this
                rw [this] at mod4
                ring_nf at mod4
                rw [hc] at mod4
                have : ∃ d, x * 2 - (2 * c + 1) = 2 * d + 1 := by
                  use x - c - 1
                  omega
                obtain ⟨d, hd⟩ := this
                rw [hd, pow_add, pow_mul, pow_one, (by norm_num : (3 : ZMod 4) ^ 2 = 9)] at mod4
                have : 9 ≡ 1 [MOD 4] := by
                  decide
                rw [← ZMod.eq_iff_modEq_nat] at this
                simp only [Nat.cast_ofNat, Nat.cast_one] at this
                rw [this] at mod4
                ring_nf at mod4
                have : 1 ≡ 3 [MOD 4] := by
                  rw [← ZMod.eq_iff_modEq_nat]
                  exact_mod_cast mod4
                contradiction
  --Conversely, if (x, y, z) = (2, 1, 1), we can easily check that the equation holds.
    · intro h
      simp only [Prod.mk_one_one, Prod.mk.injEq, Prod.mk_eq_one] at h
      rw [h.1, h.2.1, h.2.2]
      ring_nf