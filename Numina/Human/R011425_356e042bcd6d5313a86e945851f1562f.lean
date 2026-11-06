import Mathlib

-- useful theorem that works on arbitary lists of natural numbers:
-- says that `Nat.ofDigits 10 L ≡ L.sum [MOD 9]`
theorem ofDigits_and_sum_eq_mod_9 (L: List ℕ):
    (Nat.ofDigits 10 L) % 9 = L.sum % 9 := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons head tail ih => simp [Nat.ofDigits]; omega

-- another theorem about arbitrary lists of natural numbers:
-- basically says that `Nat.ofDigits 10 L ≡ L.alternatingSum [MOD 11]`
-- (but converts natural numbers to integers before calculations)
theorem ofDigits_and_sum_mod_11 (L: List ℕ):
    (@Nat.cast ℤ instNatCastInt (Nat.ofDigits 10 L)) % 11 =
    (L.map (fun n => (n: ℤ))).alternatingSum % 11 := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons head tail ih => simp [Nat.ofDigits]; simp at ih; omega

-- I needed this theorem, because that `flatMap` sprung from somewhere,
-- so I worked around it
theorem aux (L: List ℕ):
    L.reverse.flatMap (fun a => [(a: ℤ)]) = (L.flatMap (fun a => [(a: ℤ)])).reverse := by
  induction L with
  | nil => simp
  | cons head tail ih => simp_all


/- Denote by $f(n)$ the integer obtained by reversing the digits of a positive integer $n$. Find the greatest integer that is certain to divide $n^{4}-f(n)^{4}$ regardless of the choice of $n$. -/
theorem number_theory_258446 (f : ℕ → ℕ)
    (hf : ∀ (n: ℕ), f n = Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) :
    IsGreatest { k | ∀ (n: ℕ), k ∣ ((n ^ 4): ℤ) - ((f n ^ 4): ℤ)} 99 := by

  unfold IsGreatest upperBounds
  constructor

  . simp
    intros n

    -- let's prove that `n ≡ f n [MOD 9]` first
    have H: (n: ℤ) % 9 = (f n: ℤ) % 9 := by
      -- let's cast the goal from integers to natural numbers
      norm_cast
      -- rewrite that `f n` with actual definition
      rw [hf]
      -- use the theorem on the list `(Nat.digits 10 n).reverse`
      rw [ofDigits_and_sum_eq_mod_9]
      -- sum of list of natural numbers doesn't change,
      -- if the list is reversed
      rw [List.sum_reverse]
      -- and this is library lemma
      rw [<- Nat.modEq_nine_digits_sum]

    -- prove that `n - f n` is divided by `9`
    have H0: ((n: ℤ) - (f n: ℤ)) % 9 = 0 :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mp H

    -- and that expression `n - f n` is a factor in the expression `n ^ 4 - f n ^ 4`,
    -- therefore the bigger expression is divided by `9` too
    have H1 (x y: ℤ): x ^ 4 - y ^ 4 = (x - y) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) := by ring

    have H2: 9 ∣ (n: ℤ) - (f n: ℤ) :=
      Int.ModEq.dvd H.symm

    have H3: 9 ∣ (n: ℤ) ^ 4 - ↑(f n) ^ 4 := by
      rw [H1]
      apply Dvd.dvd.mul_right H2


    -- two useful lemmas, will be used in proof of the next lemma
    have H4 (a b: ℤ): 11 ∣ (a + b) ↔ (a % 11 + b % 11) % 11 = 0 := by omega
    have H5 (a b: ℤ): 11 ∣ (a - b) ↔ (a % 11 - b % 11) % 11 = 0 := by omega

    -- let's prove that `n + f n ≡ 0 [MOD 11]` or `n - f n ≡ [MOD 11]`
    -- this time we work with integers, no casting to natural numbers
    have H6: ((n: ℤ) + (f n: ℤ)) % 11 = 0 ∨ ((n: ℤ) - (f n: ℤ)) % 11 = 0 := by
      -- let's use the definition (or property) of function `f`
      rw [hf]
      simp
      -- replace `n` with their lists of digits, converted back to digits
      -- that's because we want to work with lists
      nth_rw 1 3 [<- Nat.ofDigits_digits 10 n]
      -- depending on the parity of this long expression
      -- the change will be different (because of power of `-1` later)
      obtain H7 | H7 := Nat.even_or_odd
          (List.map (List.length ∘ fun (a: ℕ) => [(a: ℤ)]) (Nat.digits 10 n)).sum
      . obtain ⟨d, H7⟩ := H7
        left
        -- rewrite by that result of `omega` first (lemma `H4`)
        -- then two times using lemma `ofDigits_and_sum_mod_11`
        rw [H4, ofDigits_and_sum_mod_11, ofDigits_and_sum_mod_11]
        simp
        -- swap `reverse` and `flatMap`, to use theorem `List.alternatingSum_reverse`
        rw [aux, List.alternatingSum_reverse]
        simp
        -- use the parity of the exponent of `-1`
        rw [H7]
        simp
      . -- the same idea here too
        obtain ⟨d, H7⟩ := H7
        right
        rw [H5, ofDigits_and_sum_mod_11, ofDigits_and_sum_mod_11]
        simp
        rw [aux, List.alternatingSum_reverse]
        simp
        -- there little help is need (to change the exponent into obviously even form)
        rw [H7, show 2 * d + 1 + 1 = 2 * (d + 1) by ring]
        simp

    -- `n + f n ≡ [MOD 11]` or `n - f n ≡ [MOD 11]`
    -- in both cases the expression is a factor of the `n ^ 2 - f n ^ 2`
    -- therefore it is also divided by `11`
    have H7: 11 ∣ ((n: ℤ) ^ 2 - (f n: ℤ) ^ 2) := by
      rw [sq_sub_sq]
      obtain H8 | H8 := H6
      . have H9: 11 ∣ (n: ℤ) + (f n: ℤ) := Int.dvd_of_emod_eq_zero H8
        apply Dvd.dvd.mul_right H9
      . have H10: 11 ∣ (n: ℤ) - (f n: ℤ) := Int.dvd_of_emod_eq_zero H8
        apply Dvd.dvd.mul_left H10

    -- and the expression `n ^ 2 - f n ^ 2` is a factor of
    -- the expression in the goal
    have H8 (x y: ℤ): x ^ 4 - y ^ 4 = (x ^ 2 - y ^ 2) * (x ^ 2 + y ^ 2) := by ring

    -- therefore this expression is divided by `11`
    have H9: 11 ∣ (n: ℤ) ^ 4 - (f n: ℤ) ^ 4 := by
      rw [H8]
      apply Dvd.dvd.mul_right H7

    -- rewrite `99` as the product of two relative primes
    rw [show (99: ℤ) = 9 * 11 by norm_num]

    -- prove that `9` and `11` are relative primes,
    -- casting them to natural numbers and then using `norm_num`
    have H10: IsCoprime (9: ℤ) 11 := by
      rw [Int.coprime_iff_nat_coprime]
      simp
      norm_num


    -- and we get the necessary result
    exact IsCoprime.mul_dvd H10 H3 H9

  . -- this direction of the proof is much easier
    simp
    intros n H

    -- the expression `n - f n` is `9999` when `n = 10`
    have H1 := H 10
    rw [hf] at H1
    simp at H1
    rw [show Nat.ofDigits 10 [1, 0] = 1 by rfl] at H1
    simp at H1

    -- the expression `n - f n` is `173745` when `n = 21`
    have H2 := H 21
    rw [hf] at H2
    simp at H2
    rw [show Nat.ofDigits 10 [2, 1] = 12 by rfl] at H2
    simp at H2

    -- the greatest common divisor of these two values is `99`
    -- and that means that `n` divides `99`
    have H3 := Int.dvd_gcd H1 H2
    norm_num at H3

    -- therefore, `n` can't be bigger than value `99`
    apply Int.le_of_dvd (by norm_num) H3