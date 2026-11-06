import Mathlib

open Nat

/-
Find the number of positive integer divisors of 12! that leave a remainder of 1 when divided by 3 .

The answer is 66.
-/
theorem number_theory_609540 : ((divisors 12!).filter (fun n ↦ n ≡ 1 [MOD 3])).card = 66 := by

  -- Factor 12! as 3^5 * 1971200
  have claim1 : 12! = 3^5 * 1971200 := by norm_num; decide

  -- We claim that the set of positive integer divisors of 12! that leave a remainder of 1 when divided by 3
  -- is the same as the set of positive integer divisors of 1971200 that leave a remaminder of 1 when divided by 3.
  have claim2 : (divisors 12!).filter (fun n ↦ n ≡ 1 [MOD 3]) =
                (divisors 1971200).filter (fun n ↦ n ≡ 1 [MOD 3]) := by

    -- We prove set equality by set inclusion in both directions.
    apply Finset.ext
    intro a
    constructor
    . -- Take a from the set of positive integer divisors of 12! that leave a remainder of 1 when divided by 3.
      simp
      intro h1 h2 h
      -- Show that a divides 1971200 and leaves a reaminder of 1 when divided by 3.
      constructor
      . rw [claim1] at h1
        -- a must be coprime with 3^5. Otherwise, a is divisible by 3 and leaves a remainder of 0 when divided by 3.
        have : a.Coprime (3^5) := by
          apply Prime.coprime_pow_of_not_dvd prime_three
          rw [← modEq_zero_iff_dvd]
          intro ha
          have : 0 ≡ 1 [MOD 3]:= by exact ModEq.trans (id (ModEq.symm ha)) h
          rw [modEq_iff_dvd] at this
          simp at this
          revert this
          decide
        -- Since a is coprime with 3^5, if a divides 3^5 * 1971200, it must divide 1971200.
        exact Coprime.dvd_of_dvd_mul_left this h1
      . -- a leaves a remainder of 1 when divided by 3 by assumption.
        assumption
    . -- Take a from the set of positive integer divisors of 1971200 that leave a remainder of 1 when divided by 3.
      simp
      intro ha hamod
      constructor
      . rw [claim1]
        constructor
        . -- Since 12! = 3^5 * 1971200, a divides 1971200 implies a divides 12!
          exact Dvd.dvd.mul_left ha (3 ^ 5)
        . decide
      . -- a leaves a remainder of 1 when divided by 3 by assumption.
        exact hamod

  -- Using the above claim, we rewrite the problem statement as:
  -- The number of positive integer divisors of 1971200 that leave a remainder of 1 when divided by 3 is 66.
  rw [claim2]

  -- Factor 1971200 as a product of its prime powers: 2^10 * 5^2 * 7^1 * 11^1
  have hnum : 1971200 = 2^10 * (5^2 * (7^1 * 11^1)) := by norm_num

  -- We claim that the set of positive integer divisors of 1971200 that leave a remainder of 1 when divided by 3 is
  -- the same as the set of positive integers 2^a * 5^b * 7^c * 11^c where a, b, c, d are natural numbers such that
  -- a < 11, b < 3, c < 2, d < 2 and a+b+d is even.
  have claim3 : (divisors 1971200).filter (fun n ↦ n ≡ 1 [MOD 3]) =
                (((Finset.range 11) ×ˢ (Finset.range 3) ×ˢ (Finset.range 2) ×ˢ (Finset.range 2)).filter (fun (a,b,c,d) ↦ Even (a + b + d))).image
                 (fun (a,b,c,d) ↦ 2^a * 5^b * 7^c * 11^d) := by

    -- We prove set equality by set inclusion in both directions.
    apply Finset.ext
    intro a

    -- We claim that if a = 2^e2 * 5^e5 * 7^e7 * 11^e11 for some natural numbers e2, e5, e7, 11,
    -- then a is congruent 2 ^ (e2 + e5 + e11) modulo 3.
    have claimA {e2 e5 e7 e11 : ℕ} (ha : a = 2^e2 * 5^e5 * 7^e7 * 11^e11) : a ≡ 2 ^ (e2 + e5 + e11) [MOD 3] := by
      calc
      _ = 2^e2 * 5^e5 * 7^e7 * 11^e11 := by rw [ha]
      _ = 2^e2 * 5^e5 * 11^e11 * 7^e7 := by ring
      _ ≡ 2^e2 * 5^e5 * 11^e11 * 1^e7 [MOD 3] := by
            have hh : 7^e7 ≡ 1^e7 [MOD 3] := by suffices 7 ≡ 1 [MOD 3] by exact ModEq.pow e7 this
                                                decide
            exact Nat.ModEq.mul_left _ hh
      _ = 2^e2 * 5^e5 * 11^e11 := by ring
      _ ≡ 2^e2 * 5^e5 * 2^e11 [MOD 3] := by
            have hh : 11^e11 ≡ 2^e11 [MOD 3] := by suffices 11 ≡ 2 [MOD 3] by exact ModEq.pow e11 this
                                                   decide
            exact Nat.ModEq.mul_left _ hh
      _ = 2^e2 * 2^e11 * 5^e5 := by ring
      _ ≡ 2^e2 * 2^e11 * 2^e5 [MOD 3] := by
            have hh : 5^e5 ≡ 2^e5 [MOD 3] := by suffices 5 ≡ 2 [MOD 3] by exact ModEq.pow e5 this
                                                decide
            exact Nat.ModEq.mul_left _ hh
      _ = 2^(e2 + e5 + e11) := by ring

    constructor
    . -- Take a from the set of positive integer divisors of 1971200 that leave a remainder of 1 when divided by 3.
      -- Rewrite 1971200 as a product of prime powers: 2^10 * (5^2 * (7^1 * 11^1)).
      -- Then a divides 1971200 means that there exist natural numbers e2 ≤ 10, e5 ≤ 2, e7 ≤ 1, e11 ≤ 1 such that
      -- a = 2^e2 * (5^e5 * (7^e7 * 11^e11)).
      simp
      rw [hnum]
      intro ha hamod
      rw [dvd_mul] at ha
      obtain ⟨ a2, ⟨ z2, ⟨ ha2, ⟨ hz2l, hz2r ⟩ ⟩ ⟩ ⟩ := ha
      rw [dvd_mul] at hz2l
      obtain ⟨ a5, ⟨ z5, ⟨ ha5, ⟨ hz5l, hz5r ⟩ ⟩ ⟩ ⟩ := hz2l
      rw [dvd_mul] at hz5l
      obtain ⟨ a7, ⟨ a11, ⟨ ha7, ⟨ ha11, hz7r ⟩ ⟩ ⟩ ⟩ := hz5l
      have he2 : ∃ k : ℕ, k ≤ 10 ∧ a2 = 2 ^ k := by
        rw [dvd_prime_pow prime_two] at ha2
        exact ha2
      have he5 : ∃ k : ℕ, k ≤ 2 ∧ a5 = 5 ^ k := by
        rw [dvd_prime_pow prime_five] at ha5
        exact ha5
      have he7 : ∃ k : ℕ, k ≤ 1 ∧ a7 = 7 ^ k := by
        rw [@dvd_prime_pow 7 (by decide)] at ha7
        exact ha7
      have he11 : ∃ k : ℕ, k ≤ 1 ∧ a11 = 11 ^ k := by
        rw [@dvd_prime_pow 11 (by decide)] at ha11
        exact ha11

      -- Extract the exponents e2, e5, e7, e11 for primes 2, 5, 7, 11
      -- so that a = 2^e2 * 5^e5 * 7^e7 *11^e11
      obtain ⟨ e2, ⟨ he2l, he2r ⟩ ⟩ := he2
      obtain ⟨ e5, ⟨ he5l, he5r ⟩ ⟩ := he5
      obtain ⟨ e7, ⟨ he7l, he7r ⟩ ⟩ := he7
      obtain ⟨ e11, ⟨ he11l, he11r ⟩ ⟩ := he11
      use e2
      use e5
      use e7
      use e11
      have : a = 2^e2 * 5^e5 * 7^e7 * 11^e11 := by
        rw [← he2r, ← he5r, ← he7r, ← he11r]
        rw [← hz7r] at hz5r
        rw [← hz5r] at hz2r
        rw [← hz2r]
        ring

      constructor
      . constructor
        . refine And.intro (lt_add_one_of_le he2l) ?_
          refine And.intro (lt_add_one_of_le he5l) ?_
          refine And.intro (lt_add_one_of_le he7l) ?_
          exact lt_add_one_of_le he11l
        . -- We show that e2 + e5 + e11 is even.
          by_contra hodd
          rw [not_even_iff_odd] at hodd
          obtain ⟨ k, hk ⟩ := hodd
          -- By claimA, we have a ≡ 2 ^ (e2 + e5 + e11) [MOD 3]
          obtain claimA' := claimA this
          rw [hk] at claimA'
          have : 2 ^ (2 * k + 1) ≡ 2 [MOD 3] := by
            calc
              2 ^ (2*k + 1) = (2 ^ 2)^k * 2^1 := by rw [pow_add, pow_mul];
              _ = 4^k * 2 := by norm_num
              _ ≡ 1^k * 2 [MOD 3] := by have : 4^k ≡ 1^k [MOD 3] := by suffices 4 ≡ 1 [MOD 3] by exact ModEq.pow k this
                                                                       decide
                                        exact ModEq.mul this rfl
              _ ≡ 2 [MOD 3] := by ring_nf; decide
          obtain bad := ModEq.trans claimA' this
          obtain cont := ModEq.trans (ModEq.symm hamod) bad
          revert cont
          decide
      . -- Show that a = 2^e2 * 5^e5 * 7^e7 * 11^e11
        rw [← he2r, ← he5r, ← he7r, ← he11r]
        rw [← hz7r] at hz5r
        rw [← hz5r] at hz2r
        rw [← hz2r]
        ring
    . simp
      -- Take natural numbers e2 ≤ 10, e5 ≤ 2, e7 ≤ 1, e11 ≤ 1 such that e2 + e5 + e11 is even
      -- a = 2^e2 * 5^e5 * 7^e7 * 11^e11.
      intro e2 e5 e7 e11 he2 he5 he7 he11
      intro heven
      intro ha
      constructor
      . -- Show that a divides 1971200.
        rw [hnum]
        repeat rw [← mul_assoc]
        rw [← ha]
        have plemma {p k n : ℕ} (hp : Nat.Prime p) (h : k ≤ n) : p ^ k ∣ p ^ n := by
          rw [Prime.pow_dvd_iff_le_factorization]
          simp
          rw [Prime.factorization_self]
          linarith
          repeat assumption
          suffices p ≠ 0 by exact pow_ne_zero n this
          exact Nat.Prime.ne_zero hp

        repeat apply mul_dvd_mul
        apply plemma prime_two; linarith
        apply plemma prime_five; linarith
        apply plemma (by decide); linarith
        apply plemma (by decide); linarith

      . -- Show that a leaves a remainder of 1 when divided by 3.
        obtain claimA' := by exact claimA (Eq.symm ha)
        obtain ⟨ k, hk ⟩ := heven
        ring_nf at hk
        rw [hk] at claimA'
        rw [mul_comm] at claimA'
        rw [pow_mul] at claimA'
        norm_num at claimA'
        have : 4^k ≡ 1^k [MOD 3] := by suffices 4 ≡ 1 [MOD 3] by exact ModEq.pow k this
                                       decide
        obtain result := ModEq.trans claimA' this
        simp at result
        assumption

  -- Using the above claim, we write the problem statement as:
  -- The number of positive integers 2^a * 5^b * 7^c * 11^c where a, b, c, d are natural numbers such that
  -- a < 11, b < 3, c < 2, d < 2 and a+b+d is even is 66.
  rw [claim3]
  -- The proof can now be completed by a simple case analysis.
  decide
  done
