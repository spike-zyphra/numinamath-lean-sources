import Mathlib

/- 4. Find all integer pairs $(x, y)$, such that

$$

3^{4} \times 2^{3}\left(x^{2}+y^{2}\right)=x^{3} y^{3} \text {. }

$$
 -/
theorem algebra_208553 (x y : ℤ) : 3^4 * 2^3 * (x^2 + y^2) = x^3 * y^3 ↔ (x = -6 ∧ y = -6) ∨ (x = 0 ∧ y = 0) ∨ (x = 6 ∧ y = 6) := by
--We prove first that the equality implies that x, y can only be both 0, 6 or -6, and then that these three pairs satisfy the equation.
  constructor
--We first consider the case where either x or y are 0.
  · by_cases hxyzero : x = 0 ∨ y = 0
    · rcases hxyzero with hxyzero | hxyzero
--If any of x and y is zero, substituting it in the equation gives us that the other one is also zero.
      all_goals
        subst hxyzero
        ring_nf
        simp
--We now assume that x and y are both nonzero. We will prove that they are both positive or both negative.
    · simp only [not_or] at hxyzero
      rw [← ne_eq, ← ne_eq] at hxyzero
      intro eq
      have : 0 < x ^ 3 * y ^ 3 := by
        rw [← eq]
        simp only [Int.reducePow, Int.reduceMul, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
        rw [← sq_pos_iff, ← sq_pos_iff] at hxyzero
        linarith
      rw [mul_pos_iff] at this
--We can assume, withouth loss of generality, that x and y are both positive.
      suffices pos (x y : ℤ) (heq : 3 ^ 4 * 2 ^ 3 * (x ^ 2 + y ^ 2) = x ^ 3 * y ^ 3) : (0 < x ∧ 0 < y) → (x = -6 ∧ y = -6 ∨ x = 0 ∧ y = 0 ∨ x = 6 ∧ y = 6)
      · rcases this with pospos | negneg
        · rw [Odd.pow_pos_iff (by decide : Odd 3), Odd.pow_pos_iff (by decide : Odd 3)] at pospos
          exact pos x y eq pospos
        · rw [Odd.pow_neg_iff (by decide : Odd 3), Odd.pow_neg_iff (by decide : Odd 3)] at negneg
          set xm := -x with hx
          set ym := -y with hy
          have : 0 < xm ∧ 0 < ym := by
            constructor
            · rw [hx]
              linarith
            · rw [hy]
              linarith
          have eq' : 3 ^ 4 * 2 ^ 3 * (xm ^ 2 + ym ^ 2) = xm ^ 3 * ym ^ 3 := by
            rw [hx, hy, neg_sq, neg_sq, Odd.neg_pow (by decide), Odd.neg_pow (by decide), neg_mul_neg]
            exact eq
          apply pos xm ym eq' at this
          rw [hx, hy] at this
          rw [neg_inj, neg_inj, neg_eq_zero, neg_eq_zero, neg_eq_iff_eq_neg, neg_eq_iff_eq_neg] at this
          tauto
--Since x and y are both positive, we will prove that they are both equal to 6.
      · intro h
        right; right
--We observe that 3^4 divides both sides of the equation. This means that at least one of x and y is divisible by 3.
        have : 3 ^ 4 ∣ x ^ 3 * y ^ 3 := by
          use 2 ^ 3 * (x ^ 2 + y ^ 2)
          rw [← heq]
          ring_nf
--We prove that, in fact, both x and y are divisible by 3. If this were not the case, computing the 3-adic valuations of both sides of the equation would give us a contradiction.
        have : 3 ∣ x ∧ 3 ∣ y := by
          by_contra h
          simp only [not_and] at h
          have eq_3adic_val : padicValInt 3 (3 ^ 4 * 2 ^ 3 * (x ^ 2 + y ^ 2)) = padicValInt 3 (x ^ 3 * y ^ 3) := by
              rw [heq]
          by_cases hx : 3 ∣ x
          · have := h hx
            have h3notdvd : ¬ 3 ∣ (x ^ 2 + y ^ 2) := by
              intro hfalse
              have hx2 : 3 ∣ x ^ 2 := by
                rw [Prime.dvd_pow_iff_dvd (by simp only [Int.prime_ofNat_iff]; decide) (by decide)]
                exact hx
              apply dvd_sub hfalse at hx2
              ring_nf at hx2
              rw [Prime.dvd_pow_iff_dvd (by simp only [Int.prime_ofNat_iff]; decide) (by decide)] at hx2
              contradiction
            have lhs_3adic_val : padicValInt 3 (3 ^ 4 * 2 ^ 3 * (x ^ 2 + y ^ 2)) = 4 := by
              rw [padicValInt.mul (by omega) (by omega), padicValInt.mul (by omega) (by omega), (by native_decide : padicValInt 3 (3 ^ 4) + padicValInt 3 (2 ^ 3) = 4)]
              simp only [add_right_eq_self]
              exact padicValInt.eq_zero_of_not_dvd h3notdvd
            rw [lhs_3adic_val] at eq_3adic_val
            have rhs_3adic_val : 3 ∣ padicValInt 3 (x ^ 3 * y ^ 3) := by
              unfold padicValInt
              rw [← mul_pow, Int.natAbs_pow, padicValNat.pow]
              · simp only [dvd_mul_right]
              · unfold Ne
                rw [Int.natAbs_eq_zero]
                simp only [mul_eq_zero, not_or]
                omega
            rw [← eq_3adic_val] at rhs_3adic_val
            contradiction
          by_cases hy : 3 ∣ y
          · have h3notdvd : ¬ 3 ∣ (x ^ 2 + y ^ 2) := by
              intro hfalse
              have hx2 : 3 ∣ y ^ 2 := by
                rw [Prime.dvd_pow_iff_dvd (by simp only [Int.prime_ofNat_iff]; decide) (by decide)]
                exact hy
              apply dvd_sub hfalse at hx2
              ring_nf at hx2
              rw [Prime.dvd_pow_iff_dvd (by simp only [Int.prime_ofNat_iff]; decide) (by decide)] at hx2
              contradiction
            have lhs_3adic_val : padicValInt 3 (3 ^ 4 * 2 ^ 3 * (x ^ 2 + y ^ 2)) = 4 := by
              rw [padicValInt.mul (by omega) (by omega), padicValInt.mul (by omega) (by omega), (by native_decide : padicValInt 3 (3 ^ 4) + padicValInt 3 (2 ^ 3) = 4)]
              simp only [add_right_eq_self]
              exact padicValInt.eq_zero_of_not_dvd h3notdvd
            rw [lhs_3adic_val] at eq_3adic_val
            have rhs_3adic_val : 3 ∣ padicValInt 3 (x ^ 3 * y ^ 3) := by
              unfold padicValInt
              rw [← mul_pow, Int.natAbs_pow, padicValNat.pow]
              · simp only [dvd_mul_right]
              · unfold Ne
                rw [Int.natAbs_eq_zero]
                simp only [mul_eq_zero, not_or]
                omega
            rw [← eq_3adic_val] at rhs_3adic_val
            contradiction
          · have h3dvd : 3 ∣ x ^ 3 * y ^ 3 := by
              use 3 ^ 3 * 2 ^ 3 * (x ^ 2 + y ^ 2)
              rw [← heq]
              ring_nf
            have h3notdvd : ¬ 3 ∣ x ^ 3 * y ^ 3  := by
              apply Prime.not_dvd_mul
              · simp; decide
              · intro hdvd
                apply Prime.dvd_of_dvd_pow at hdvd
                contradiction
                simp; decide
              · intro hdvd
                apply Prime.dvd_of_dvd_pow at hdvd
                contradiction
                simp; decide
            contradiction
--We can now divide the equation by 3^6, since it divides both sides.
        obtain ⟨⟨x',hx'⟩,⟨y',hy'⟩⟩ := this
        subst hx' hy'
        rw [mul_pow, mul_pow, ← mul_add, mul_pow, mul_pow] at heq
        ring_nf at heq
        rw [(by omega : (5832 : ℤ) = 8 * 729), ← mul_assoc, ← mul_assoc, ← sub_eq_zero, ← add_mul, ← sub_mul] at heq
        simp only [mul_eq_zero, OfNat.ofNat_ne_zero, or_false] at heq
        rw [sub_eq_zero, ← add_mul] at heq
        by_cases hxley : x' ≤ y'
--From the new equation we obtain a bound for x' and y'. Namely, if x' ≤ y', then x' ≤ 2.
        · have le : (x' ^ 2 + y' ^ 2) * 8 ≤ (y' ^ 2) * 16 := by
            rw [(by omega : (16 : ℤ) = 2 * 8), ← mul_assoc, mul_le_mul_right (by omega), mul_two]
            gcongr
            omega
          rw [heq] at le
          rw [mul_comm, pow_three, ← mul_assoc, ← pow_two, mul_assoc, mul_le_mul_left (by apply pow_pos; omega)] at le
          have le2 : x' ^ 4 ≤ 16 := by
            apply le_trans _ le
            rw [(by omega : 4 = 1 + 3), pow_add, pow_one, mul_le_mul_right (by apply pow_pos; omega)]
            exact hxley
          rw [(by omega : (16 : ℤ) = (2 ^ 2) ^ 2), (by omega : 4 = 2 * 2), pow_mul, sq_le_sq] at le2
          simp only [abs_pow, sq_abs, Nat.abs_ofNat] at le2
          rw [sq_le_sq] at le2
          have : 0 < x' := by omega
          simp only [Nat.abs_ofNat, this] at le2
          have : x' ≤ 2 := by
            unfold abs at le2
            simp only [sup_le_iff] at le2
            linarith
--We now consider all possible cases for x' and y'. Only x'=y'=2 gives a solution.
          interval_cases x'
          · ring_nf at heq le
            interval_cases y'
            all_goals omega
          · ring_nf at heq le
            rw [(by omega : (16 : ℤ) = 2 * 8), mul_le_mul_right (by omega)] at le
            interval_cases y'
            all_goals omega
--We repeat the same argument, but with the roles of x' and y' reversed.
        · have le : (x' ^ 2 + y' ^ 2) * 8 ≤ (x' ^ 2) * 16 := by
            rw [(by omega : (16 : ℤ) = 2 * 8), ← mul_assoc, mul_le_mul_right (by omega), mul_two]
            gcongr
            omega
            linarith
          rw [heq] at le
          rw [pow_three, ← mul_assoc, ← pow_two, mul_assoc, mul_le_mul_left (by apply pow_pos; omega)] at le
          have le2 : y' ^ 4 ≤ 16 := by
            apply le_trans _ le
            rw [(by omega : 4 = 1 + 3), pow_add, pow_one, mul_le_mul_right (by apply pow_pos; omega)]
            linarith
          rw [(by omega : (16 : ℤ) = (2 ^ 2) ^ 2), (by omega : 4 = 2 * 2), pow_mul, sq_le_sq] at le2
          simp only [abs_pow, sq_abs, Nat.abs_ofNat] at le2
          rw [sq_le_sq] at le2
          have : 0 < y' := by omega
          simp only [Nat.abs_ofNat, this] at le2
          have : y' ≤ 2 := by
            unfold abs at le2
            simp only [sup_le_iff] at le2
            linarith
          interval_cases y'
          · ring_nf at heq le
            interval_cases x'
            all_goals omega
          · ring_nf at heq le
            rw [(by omega : (16 : ℤ) = 2 * 8), mul_le_mul_right (by omega)] at le
            have : x' = 2 := by omega
            subst this
            omega
--To conclude, we check that the three given pairs for x and y are indeed solutions.
  · intro sol
    rcases sol with sol | sol | sol
    all_goals
      obtain ⟨solx, soly⟩ := sol
      subst solx soly
      rfl