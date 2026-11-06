import Mathlib

/- Find the smallest two-digit prime number such that reversing the digits of the number produces a composite number. -/
theorem algebra_12290 :
    IsLeast {p | p.Prime ∧ (Nat.digits 10 p).length = 2 ∧ ¬(Nat.Prime (Nat.ofDigits 10 (List.reverse (Nat.digits 10 p))))} 19 := by
  -- let's list primes between 10 and 20: 11,13,17,19
  have h1: ∀n:ℕ, n ≥ 10 → n ≤ 20 → Nat.Prime n → n = 11 ∨ n = 13 ∨ n = 17 ∨ n = 19 := by
    decide
  -- and try if they satisfy reverse composite.
  have h2: Nat.Prime (Nat.ofDigits 10
    (List.reverse (Nat.digits 10 11))) := by
    simp; rw [Nat.ofDigits]; simp
    -- 11 reverse is still 11, not composite.
    norm_num
  have h3: Nat.Prime (Nat.ofDigits 10
    (List.reverse (Nat.digits 10 13))) := by
    simp; rw [Nat.ofDigits]; simp;
    -- 13 reverse is 31, not composite.
    norm_num
  have h4: Nat.Prime (Nat.ofDigits 10
    (List.reverse (Nat.digits 10 17))) := by
    simp; rw [Nat.ofDigits]; simp;
    -- 17 reverse is 71, not composite.
    norm_num
  have h5': ¬Nat.Prime (Nat.ofDigits 10 [1, 9]) := by
    rw [Nat.ofDigits]; simp;
    -- 19 reverse is 91 = 13x7, composite.
    norm_num
  -- so we can claim 19 is the smallest number we find.
  rw [IsLeast, lowerBounds]; simp
  constructor
  · exact ⟨(by norm_num), h5'⟩
  · intro a pa ha renp
    -- a has two digits, so a is between 10 and 99
    have age: a ≥ 10 := by
      have anz: a ≠ 0 := by
        exact Nat.Prime.ne_zero pa
      rw [Nat.digits_len 10 a (by norm_num) anz] at ha
      have ht1: Nat.log 10 a = 1 := by
        have: 1 = 2-1 := by norm_num
        rw [this, ← ha]; simp
      have ht2: Nat.log 10 10 = 1 := by
        apply Nat.log_eq_one_iff'.mpr (by norm_num)
      by_contra! hc
      have ht3: Nat.log 10 a < Nat.log 10 10 := by
        have: 10 = 10 ^ 1 := by ring
        rw [this, ← ht2] at hc
        exact Nat.log_lt_of_lt_pow anz hc
      rw [ht1, ht2] at ht3
      norm_num at ht3
    have alt: a < 100 := by
      have: 100 = (8+2)^(Nat.digits (8+2) a).length := by
        simp; rw [ha]; simp
      rw [this]
      exact Nat.lt_base_pow_length_digits'
    -- now we need prove a ≥ 19. if a ≥ 20, then certainly 19 ≤ a. and if a ≤ 20, then we can use lemma h1.
    by_cases hha: a > 20
    · linarith [hha]
    · push_neg at hha
      have aeq := h1 a age hha pa
      rcases aeq with a11 | a13 | a17 | a19
      -- a cannot be 11,13 or 17, because their reverse are not composite.
      · exfalso; rw [a11] at renp; contradiction
      · exfalso; rw [a13] at renp; contradiction
      · exfalso; rw [a17] at renp; contradiction
      -- and a can only be 19, therefore 19 ≤ 19
      · rw [a19]