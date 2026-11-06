import Mathlib

/- Problem 1. Find all pairs $(x, y)$ of integers that satisfy the equation


$$

x^{2} y+y^{2}=x^{3} \text {. }

$$


(Daniel Paleka) -/
theorem algebra_244376 (x y : ℤ) : x^2 * y + y^2 = x^3 ↔ (x = 0 ∧ y = 0) ∨ (x = -4 ∧ y = -8)
  := by
    constructor
    · intro aa
      -- When x = 0, it's easy to see that y = 0 works
      by_cases h : x = 0
      · simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_add,
        pow_eq_zero_iff, true_and, Int.reduceNeg, zero_eq_neg, false_and, or_false] at *
        exact aa
      -- So consider when x ≠ 0
      · refine Or.inr ?_

        -- We have that x ∣ y
        have x_pow_dvd : x ^ 2 ∣ x ^3 := Dvd.intro x rfl
        rw [←aa] at x_pow_dvd
        have x_dvd_y : x ^ 2 ∣ y ^ 2
          := (Int.dvd_add_right <| Int.dvd_mul_right (x ^ 2) y).mp x_pow_dvd
        have x_dvd_y' : x ∣ y := (Int.pow_dvd_pow_iff (by linarith)).mp x_dvd_y

        -- So we can write y = k * x for some (k : ℤ)
        obtain ⟨k, kh⟩ := exists_eq_mul_left_of_dvd x_dvd_y'
        rw [kh] at aa
        convert_to x ^ 2 * (x * k + k ^ 2) = x ^ 2 * x at aa
        · linarith

        -- Replace y in the equality with k * x
        simp only [mul_eq_mul_left_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          pow_eq_zero_iff, h, or_false] at aa
        have eqq : k ^ 2 = x * (1 - k) := by linarith

        -- Then we have that (k ^ 2) and (1 - k) are coprime
        have coprime : IsCoprime (1 - k) (k ^ 2) := by
          -- We want to treat the arguments as ℕ to use Nat.Coprime, so we match on signs
          by_cases h : k ≤ 0
          · obtain ⟨p, ph⟩ := Int.exists_eq_neg_ofNat h
            rw [Int.coprime_iff_nat_coprime, ph]
            convert_to ((1 + p)).Coprime (p ^ 2)
            · simp only [sub_neg_eq_add]
              exact rfl
            · simp only [even_two, Even.neg_pow]
              exact rfl
            -- Ignore square
            apply Nat.Coprime.pow_right 2
            -- 1 + p is Coprime with p
            exact Nat.coprime_add_self_left.mpr <| Nat.gcd_one_left p
          · lift k to ℕ with p
            · exact Int.le_of_not_le h
            rw [Int.coprime_iff_nat_coprime]
            convert_to ((p - 1)).Coprime (p ^ 2)
            · convert_to (((p - 1) : ℕ) : ℤ).natAbs = p - 1
              · rw [←Int.natAbs_neg]
                congr
                omega
              · exact rfl
            -- Ignore square
            apply Nat.Coprime.pow_right 2
            -- 1 + p is Coprime with p
            exact (Nat.coprime_self_sub_left (by omega)).mpr <| Nat.gcd_one_left p

        -- Then we have two possible values for k
        have k_dvd : (1 - k) ∣ k ^ 2 := Dvd.intro_left x (eqq.symm)
        have k_one : k - 1 = 1 ∨ 1 - k = 1 := by
          have test := (Int.isCoprime_iff_gcd_eq_one.mp coprime).symm
          have yepp := Int.gcd_eq_left k_dvd
          rw [yepp] at test

          have yep2 : 1 = ((k - 1).natAbs : ℤ) := by omega
          simp only [Int.natCast_natAbs] at yep2
          by_cases h : (1 - k) ≤ k - 1
          · simp only [abs, neg_sub, h, sup_of_le_left] at yep2
            exact Or.inl <| yep2.symm
          · simp only [not_le] at h
            have what : k - 1 ≤ 1 - k := Int.le_of_lt h
            simp [abs, what] at yep2
            exact Or.inr <| yep2.symm
        cases' k_one with ha hb
        -- In one case k = 2
        · have hk : k = 2 := by linarith
          simp only [hk, Int.reducePow, Int.reduceSub, mul_neg, mul_one] at eqq
          -- So x = -4
          have x_eq : x = -4 := by linarith
          -- So y = -8
          simp only [hk, x_eq, Int.reduceNeg, mul_neg, Int.reduceMul] at kh
          exact ⟨x_eq, kh⟩
        -- In the other k = 0
        · have hk : k = 0 := by linarith
          simp only [hk, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
            mul_one] at eqq
          -- But then x = 0, contradiction
          exact False.elim <| h eqq.symm

    · intro aa
      cases' aa with ha hb
      · simp only [ha, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
      · simp only [hb, Int.reduceNeg, even_two, Even.neg_pow, Int.reducePow, mul_neg,
        Int.reduceMul, Int.reduceAdd]