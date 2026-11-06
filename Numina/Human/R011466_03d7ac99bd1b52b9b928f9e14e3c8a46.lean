import Mathlib

set_option maxHeartbeats 800000

-- this lemma finds contradition if such hypotheses are given:
-- `a`, `b`, `c` are each at least `2`, `d` is at least `1`,
-- and product of these four numbers is equal to `6`
theorem lemma_1 {a b c d: ℕ}
    (Ha: 2 ≤ a) (Hb: 2 ≤ b) (Hc: 2 ≤ c) (Hd: 1 ≤ d) (H: a * b * c * d = 6): False := by
  have Hab: 4 ≤ a * b := by nlinarith
  have Habc: 8 ≤ a * b * c := by nlinarith
  have Habcd: 8 ≤ a * b * c * d := by nlinarith
  omega

-- simple lemma, that adds one to the multiplicity of some prime factor of number `n`
-- and says that the result is at least `2`
theorem lemma_2 {p n: ℕ} (H: p ∈ n.primeFactors) (Hn: n ≠ 0): 2 ≤ n.factorization p + 1 := by
  simp
  have H0: p.Prime := Nat.prime_of_mem_primeFactors H
  have H1: p ∣ n := Nat.dvd_of_mem_primeFactors H
  exact (Nat.Prime.dvd_iff_one_le_factorization H0 Hn).mp H1

-- lemma, that finds all possible "subsets" for the given Finset,
-- if it is given by two elements it contains
-- (not necessarily they are distinct)
theorem lemma_3 (a b: ℕ) (s: Finset ℕ) (Hs: s ≤ {a, b}):
    s = {} ∨ s = {a} ∨ s = {b} ∨ s = {a, b} := by
  have aux (i: ℕ): i ∈ s → i = a ∨ i = b := by
    intros H; apply Hs at H; simp at H; exact H
  obtain H | H := em (a ∈ s) <;> obtain H0 | H0 := em (b ∈ s)
  . right; right; right
    ext i; simp; constructor <;> intro H1
    . exact aux i H1
    . obtain H1 | H1 := H1 <;> subst i <;> tauto
  . right; left
    ext i; simp; constructor <;> intro H1
    . have H2 := aux i H1
      obtain H2 | H2 := H2 <;> subst i <;> tauto
    . subst i; exact H
  . right; right; left
    ext i; simp; constructor <;> intro H1
    . have H2 := aux i H1
      obtain H2 | H2 := H2 <;> subst i <;> tauto
    . subst i; exact H0
  . left
    ext i; simp
    intro H1
    have H2 := aux i H1
    obtain H2 | H2 := H2 <;> subst i <;> tauto


/- Zhendarov R.G.

Find all natural numbers that have exactly six divisors, the sum of which is equal to 3500. -/
theorem number_theory_191306 (n : ℕ) (hn : n.divisors.card = 6) :
    ∑ d ∈ n.divisors, d = 3500 ↔ n = 1996 := by

  constructor <;> intro H

  . -- first we are going to prove the direction
    -- from the two facts about the number `n` to value of `n`

    -- `n` can't be `0`
    have H0: n ≠ 0 := by
      intros H1
      subst n
      simp at *

    -- if we know that `n` isn't zero, we can rewrite in the hypothesis `Hn`
    -- and get the much nicer form in the place of `n.divisors.card`
    rw [Nat.card_divisors H0] at hn

    -- we will take at such cases, together there are four options:
    -- 1) number `n` has cardinality of prime factor set equal to `0`
    -- 2) equal to `1`
    -- 3) equal to `2`
    -- 4) equal to `3` or more
    have H1: n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨ n.primeFactors.card = 2 ∨ 3 ≤ n.primeFactors.card := by omega
    obtain H1 | H1 | H1 | H1 := H1

    . -- when the cardinality of prime factor set is `0`,
      -- we quickly solve the goal
      rw [Finset.card_eq_zero] at H1
      rw [Nat.primeFactors_eq_empty] at H1
      simp_all

    . -- this is more adequate option, because there is one prime factor
      -- but in ths case there's no such n, so we will be trying to prove a contradiction
      exfalso

      rw [Finset.card_eq_one] at H1
      obtain ⟨a, Ha⟩ := H1
      rw [Ha] at hn
      simp at *

      -- we got the two facts: prime factor set is `{a}` and
      -- the exponent of this number is `5` (`5 + 1 = 6`, that's why)

      -- now we prove seemingly obvious fact that `n` is fifth power of this number `a`
      have H3: n = a ^ 5 := by
        apply Nat.eq_pow_of_factorization_eq_single H0
        refine Finsupp.eq_single_iff.mpr ?_
        simp
        refine ⟨?_, hn⟩
        right
        exact Ha

      -- and that this number is actually prime number
      have H2: Nat.Prime a := by
        apply Nat.prime_of_mem_primeFactors (n:= n)
        rw [Ha]
        simp

      -- now we replace the sum of all divisors with an explicit expression
      rw [H3, Nat.sum_divisors_prime_pow H2] at H
      simp at H
      repeat rw [Finset.sum_range_succ] at H
      simp at H

      -- by proving that the function is strictly increasing,
      -- we can check all cases until it becomes too big
      have H4: StrictMono (fun (i: ℕ) => 1 + i + i ^ 2 + i ^ 3 + i ^ 4 + i ^ 5) := by
        apply StrictMono.add
        . apply StrictMono.add
          . apply StrictMono.add
            . apply StrictMono.add
              . intros x y Hxy
                simp
                exact Hxy
              . exact Nat.pow_left_strictMono (by norm_num)
            . exact Nat.pow_left_strictMono (by norm_num)
          . exact Nat.pow_left_strictMono (by norm_num)
        . exact Nat.pow_left_strictMono (by norm_num)

      -- it seems that `a` has to be smaller than `5`
      have H5: a < 5 := by
        rw [<- StrictMono.lt_iff_lt H4]
        simp
        rw [H]
        simp

      -- we check all cases from `0` to `4`,
      -- even skipping checking if they are prime numbers
      interval_cases a <;> simp at H

    . -- the case with two prime factors

      -- we prove the folloring result (`H2`) to save us work on both cases:
      -- when `n = p1 * p2 ^ 2` or `n = p1 ^ 2 * p2`
      have H2: ∃ (p1 p2: ℕ), n = p1 * p2 ^ 2 ∧ p1.Prime ∧ p2.Prime ∧ p1 ≠ p2 := by

        -- we first are going to achieve result
        -- `(n.factorization x + 1) * (n.factorization y + 1) = 6`
        rw [Finset.card_eq_two] at H1
        simp at H1
        obtain ⟨x, y, Hxy, H1⟩ := H1
        rw [H1] at hn
        rw [Finset.prod_pair Hxy] at hn

        -- then we prove that `2 ≤ n.factorization x + 1` and `2 ≤ n.factorization y + 1`
        have Hx0: x ∈ n.primeFactors := by
          rw [H1]
          simp
        have Hy0: y ∈ n.primeFactors := by
          rw [H1]
          simp
        have Hx1 := lemma_2 Hx0 H0
        have Hy1 := lemma_2 Hy0 H0

        -- there are two options for values of
        -- `n.factorization x` and `n.factorization y` -
        -- basically by looking at many possible cases.
        -- at first - `n.factorization x` is at most `5` or it id more than `5`
        -- then, in the first case, we simply use `interval_cases` tactic
        -- to look at each possible case of value of `n.factorization x`
        have H2: n.factorization x = 1 ∧ n.factorization y = 2 ∨ n.factorization x = 2 ∧ n.factorization y = 1 := by
          have H3: n.factorization x ≤ 5 ∨ 5 < n.factorization x := le_or_lt (n.factorization x) 5
          obtain H3 | H3 := H3
          . simp at Hx1
            interval_cases (n.factorization x)
            . left
              omega
            . right
              omega
            . omega
            . omega
            . omega
          . nlinarith

        -- we prove that `x` and `y` are primes, that's easy
        -- because they belong to `n.primeFactors`
        have Hx2: x.Prime := Nat.prime_of_mem_primeFactors Hx0
        have Hy2: y.Prime := Nat.prime_of_mem_primeFactors Hy0

        -- than we look at each of two possible cases
        -- and give witnesses for the goal with existence statement,
        -- afterwards proving all necessary properties
        obtain ⟨H2, H3⟩ | ⟨H2, H3⟩ := H2
        . use x, y
          refine ⟨?_, Hx2, Hy2, Hxy⟩
          rw [<- Nat.factorization_prod_pow_eq_self H0]
          rw [Nat.prod_factorization_eq_prod_primeFactors]
          rw [H1, Finset.prod_pair Hxy, H2, H3]
          ring
        . use y, x
          refine ⟨?_, Hy2, Hx2, ?_⟩
          . rw [<- Nat.factorization_prod_pow_eq_self H0]
            rw [Nat.prod_factorization_eq_prod_primeFactors]
            rw [H1, Finset.prod_pair Hxy, H2, H3]
            ring
          . exact fun a => Hxy a.symm

      -- let's all this information form freshly provided fact `H2`
      obtain ⟨p1, p2, Hn, Hp1, Hp2, Hne⟩ := H2

      -- we prove the correctness of specific representation for `n.divisors`
      have H2: n.divisors = {1, p1, p2, p2 ^ 2, p1 * p2, p1 * p2 ^ 2} := by
        rw [Hn, Nat.divisors_mul, Nat.Prime.divisors Hp1, Nat.Prime.divisors_sq Hp2]
        ext x
        rw [Finset.mem_mul]
        simp
        tauto

      -- and use this representation
      rw [H2] at H

      -- this was an result, very annoying to prove
      -- but i couldn't think of any better way.
      -- the main problem is that we need to prove distinctness of
      -- all elements of the set, for this proof to work
      have H3: ∑ d ∈ {1, p1, p2, p2 ^ 2, p1 * p2, p1 * p2 ^ 2}, d =
               (1 + p1) * (1 + p2 + p2 ^ 2) := by
        have H4: 2 ≤ p1 := Nat.Prime.one_lt Hp1
        have H5: 2 ≤ p2 := Nat.Prime.one_lt Hp2
        -- first repeated appplication of library theorem `Finset.sum_insert`,
        -- which allows us to chop this sum into pieces,
        -- but we still need to prove that these pieces are distinct values
        repeat rw [Finset.sum_insert]
        . -- easy part
          simp
          ring
        . -- here lots of proof, that values are distinct, follows
          intros H6
          simp at H6
          obtain H6 | H6 := H6
          . nlinarith
          . omega
        . intros H6
          simp at H6
          obtain H6 | H6 := H6
          . apply Hne
            nlinarith
          . nlinarith
        . intros H6
          simp at H6
          obtain H6 | H6 | H6 := H6
          . nlinarith
          . nlinarith
          . nlinarith
        . intros H6
          simp at H6
          obtain H6 | H6 | H6 | H6 := H6
          . tauto
          . rw [H6] at Hp1
            apply Nat.Prime.not_prime_pow (n := 2) (by norm_num) Hp1
          . nlinarith
          . have H7: 2 ≤ p2 ^ 2 := by nlinarith
            nlinarith
        . intros H6
          simp at H6
          obtain H6 | H6 | H6 | H6 | H6 := H6 <;> nlinarith

      rw [H3] at H

      -- let's use abbreviature for the expression `1 + p2 + p2 ^ 2`
      set w := 1 + p2 + p2 ^ 2

      -- we know that `w` divides `3500`, than `w` isn't zero (of course)
      -- and that it has value bigger than `1`
      have H7: w ∣ 3500 := Dvd.intro_left _ H
      have H8: w ≠ 0 := by omega

      have H14: 1 < w := by
        unfold w
        have H15: 1 < p2 := Nat.Prime.one_lt Hp2
        omega

      -- let's prove that `2` doesn't divide `w`
      -- we look at possible cases `mod 2` and prove
      -- that in each of two cases the `w` is an odd number
      have H10: ¬ 2 ∣ w := by
        unfold w
        intro H11
        obtain H12 | H12 := Nat.even_or_odd p2
        . obtain ⟨d, H12⟩ := H12
          obtain ⟨d0, H11⟩ := H11
          rw [H12] at H11
          ring_nf at H11
          omega
        . obtain ⟨d, H12⟩ := H12
          obtain ⟨d9, H11⟩ := H11
          rw [H12] at H11
          ring_nf at H11
          omega

      -- and here we prove that `5` doesn't divide `w`
      -- with the same approach of looking at `p2 mod 5`,
      -- or at all fives cases with different remainders from dividing by `5`
      have H11: ¬ 5 ∣ w := by
        unfold w
        intro H11
        have H12 := Nat.div_add_mod p2 5
        have H13: p2 % 5 = 0 ∨ p2 % 5 = 1 ∨ p2 % 5 = 2 ∨ p2 % 5 = 3 ∨ p2 % 5 = 4 := by
          omega
        obtain ⟨d, H11⟩ := H11
        obtain H13 | H13 | H13 | H13 | H13 := H13
        . rw [H13] at H12
          rw [<- H12] at H11
          ring_nf at H11
          omega
        . rw [H13] at H12
          rw [<- H12] at H11
          ring_nf at H11
          omega
        . rw [H13] at H12
          rw [<- H12] at H11
          ring_nf at H11
          omega
        . rw [H13] at H12
          rw [<- H12] at H11
          ring_nf at H11
          omega
        . rw [H13] at H12
          rw [<- H12] at H11
          ring_nf at H11
          omega

      -- we will use this factorization
      have H9: 3500 = 2 ^ 2 * 5 ^ 3 * 7 := by norm_num

      -- let's prove the values of all prime factors of `3500`
      have H16: Nat.primeFactors 3500 = {2, 5, 7} := by
        rw [H9]
        rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
        have H17: Nat.Prime 7 := by norm_num
        have H18: Nat.primeFactors 7 = {7} := Nat.Prime.primeFactors H17
        rw [H18]
        rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
        have H19: Nat.Prime 2 := by norm_num
        have H20: Nat.Prime 5 := by norm_num
        have H21: Nat.primeFactors (2 ^ 2) = {2} := Nat.primeFactors_prime_pow (by norm_num) H19
        rw [H21]
        have H22: Nat.primeFactors (5 ^ 3) = {5} := Nat.primeFactors_prime_pow (by norm_num) H20
        rw [H22]
        ext x
        simp

      -- we prove that prime factors of `w` is a subset of
      -- prime factors of `3500`
      have H17: w.primeFactors ⊆ {2, 5, 7} := by
        rw [<- H16]
        refine Nat.primeFactors_mono ?_ (by norm_num)
        exact Dvd.intro_left _ H

      -- also, `2` isn't one of those prime factors of `w`
      -- based on the previously proven result from modularity arguments
      have H18: 2 ∉ w.primeFactors := by
        intro H19
        apply H10
        rw [Nat.mem_primeFactors_of_ne_zero H8] at H19
        tauto

      -- also, `5` isn't one of prime factors of `w`, too
      have H19: 5 ∉ w.primeFactors := by
        intro H19
        apply H10
        rw [Nat.mem_primeFactors_of_ne_zero H8] at H19
        tauto

      -- that leaves the only possible prime factor as `w` to be `7`
      -- although the proof is a bit long.
      -- as all such proofs usually do, it uses set extensionality
      have H20: w.primeFactors = {7} := by
        ext x
        constructor <;> intro H21
        . have H22: x ≠ 2 := by
            intro H23
            subst x
            tauto
          have H23: x ≠ 5 := by
            intro H24
            subst x
            tauto
          apply H17 at H21
          simp at H21 ⊢
          tauto
        . simp at H21
          subst x
          have H22: w.primeFactors ≠ ∅ := by
            intros H23
            rw [Nat.primeFactors_eq_empty] at H23
            omega
          by_contra H23
          apply H22; clear H22
          ext x
          constructor <;> intro H24
          . simp
            have H25: x = 2 ∨ x = 5 ∨ x = 7 := by
              apply H17 at H24
              simp at H24
              exact H24
            obtain H25 | H25 | H25 := H25
            . subst x; tauto
            . subst x; tauto
            . subst x; tauto
          . simp at H24

      -- let's prove that `w` is `7`
      have H22: ∃ (k: ℕ), w = 7 ^ k := by
        rw [<- Nat.factorization_prod_pow_eq_self H8]
        rw [Nat.prod_factorization_eq_prod_primeFactors]
        rw [H20]
        simp

      obtain ⟨k, H22⟩ := H22

      rw [H22, H9] at H7

      -- there are three possible cases for the exponent of `7` in `w`
      -- (let's denote it by `k`)
      -- it is zero, it is one, or it is at least two
      have H23: k = 0 ∨ k = 1 ∨ 2 ≤ k := by omega
      obtain H23 | H23 | H23 := H23

      . -- this case is easy, because `w` is bigger than `1`
        subst k
        simp at H22
        omega

      . subst k
        simp at H22

        -- if `w` or `1 + p2 + p2 ^ 2` is equal to 7,
        -- then `p1 = 1` and `p2 = 2` and from that follows
        -- the goal we want to prove - `n = 1996`
        unfold w at *
        obtain H23 | H23 | H23 := Nat.lt_trichotomy p2 2

        . -- impossible cases: `p2` too little
          interval_cases p2 <;> simp at H22

        . -- this is what we needed
          subst p2
          omega

        . -- impossible case, because `p2` is too big
          -- for `1 + p2 + p2 ^ 2` to be equal to `7`
          have H24: 3 ^ 2 ≤ p2 ^ 2 := Nat.pow_le_pow_of_le_left H23 2
          omega

      . -- `3500` can't be divided by `49`
        have H24: k = 2 + (k - 2) := by omega
        rw [H24, pow_add] at H7
        simp at H7
        obtain ⟨d, H7⟩ := H7
        rw [mul_assoc] at H7
        omega

    . -- it's clear that the only option here is to prove contradiction
      exfalso

      -- the case of at least `3` prime factors
      -- for first we prove that product of all prime factors
      -- contains at least three multiplicands
      have H2: n.primeFactors.card = (n.primeFactors.card - 3) + 1 + 1 + 1 := by omega
      repeat simp_rw [Finset.card_eq_succ] at H2
      obtain ⟨p1, t1, Hp1, Ht1, p2, t2, Hp2, Ht2, p3, t3, Hp3, Ht3, H2⟩ := H2
      subst t1 t2
      simp_rw [<- Ht1] at hn
      rw [Finset.prod_insert Hp1] at hn
      rw [Finset.prod_insert Hp2] at hn
      rw [Finset.prod_insert Hp3] at hn

      -- we prove the obvious fact that all `p1`, `p2`, `p3` is prime factors of `n`
      have H3: p1 ∈ n.primeFactors := by
        rw [<- Ht1]
        simp
      have H4: p2 ∈ n.primeFactors := by
        rw [<- Ht1]
        simp
      have H5: p3 ∈ n.primeFactors := by
        rw [<- Ht1]
        simp

      -- and that their exponent in the factorization plus one is at least `2`
      have H12: 2 ≤ n.factorization p1 + 1 := lemma_2 H3 H0
      have H13: 2 ≤ n.factorization p2 + 1 := lemma_2 H4 H0
      have H14: 2 ≤ n.factorization p3 + 1 := lemma_2 H5 H0

      -- now we prove that the remaining product is at least `1`
      have H15: t3 ⊆ n.primeFactors := by
        rw [<- Ht1]
        rw [Finset.insert_eq, Finset.insert_eq, Finset.insert_eq]
        intros x; simp; intro H15; right; right; right; exact H15

      have H16: ∀ p, p ∈ t3 → 2 ≤ n.factorization p + 1 := by
        intros p Hp
        apply H15 at Hp
        exact lemma_2 Hp H0

      have H17: 1 ≤ ∏ x ∈ t3, (n.factorization x + 1) := by
        apply Finset.prod_induction
        . intros a b Ha Hb
          exact Right.one_le_mul Ha Hb
        . simp
        . intros x Hx
          have aux := H16 x Hx
          omega

      -- and now we use the `lemma_1` to prove contradiction
      repeat rw [<- mul_assoc] at hn
      apply lemma_1 H12 H13 H14 H17 hn

  . rw [H]
    have H0: Nat.divisors 1996 = {1, 2, 4, 499, 998, 1996} := by
      ext x; constructor <;> intro H1

      . -- lets simplify a bit and prove the fact that `x` isn't zero
        simp at *
        have H2: x ≠ 0 := by
          intros H2
          subst x
          simp at H1

        -- let's work out the prime factors of 1996
        have H3: Nat.primeFactors 1996 = {2, 499} := by
          have H4: Nat.Prime 2 := by norm_num
          have H5: Nat.Prime 499 := by norm_num
          have H6: 1996 = 2 ^ 2 * 499 := by norm_num
          rw [H6]
          rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
          rw [Nat.primeFactors_prime_pow (by norm_num) H4]
          rw [show 499 = 499 ^ 1 by simp]
          rw [Nat.primeFactors_prime_pow (by norm_num) H5]
          simp; ext; simp

        -- here we prove that `x` can be expressed only by product of powers of `2` and `499`
        have H4: ∃ k1 k2, x = 2 ^ k1 * 499 ^ k2 := by
          -- first we express `x` as the product of its prime factors with correct exponents
          nth_rw 1 [<- Nat.factorization_prod_pow_eq_self H2]
          simp [Finsupp.prod]

          -- as `x` divides `1996`, that means that the set of prime factors of `x`
          -- is subset of the set of prime factors of `1996`
          have H4: x.primeFactors ⊆ Nat.primeFactors 1996 := by
            exact Nat.primeFactors_mono H1 (by norm_num)
          rw [H3] at H4

          -- that means there are four possibilites for the set of prime factors of `x`:
          -- `{}`, `{2}`, `{499}` or `{2, 499}`.
          -- we choose the correct values of exponents of `2` and `499` in each case
          apply lemma_3 at H4
          obtain H4 | H4 | H4 | H4 := H4 <;> rw [H4]
          . use 0, 0
            simp
          . use (x.factorization 2), 0
            simp
          . use 0, (x.factorization 499)
            simp
          . use (x.factorization 2), (x.factorization 499)
            simp

        obtain ⟨k1, k2, H4⟩ := H4

        -- here we look at the possibilities for each exponent
        -- in the expression for `x` (hypothesis `H4`)
        have H5: k1 = 0 ∨ k1 = 1 ∨ k1 = 2 ∨ 3 ≤ k1 := by omega
        have H6: k2 = 0 ∨ k2 = 1 ∨ 2 ≤ k2 := by omega
        obtain H5 | H5 | H5 | H5 := H5
        . subst k1
          obtain H6 | H6 | H6 := H6
          . subst k2
            tauto
          . subst k2
            tauto
          . have H7: k2 = 2 + (k2 - 2) := by omega
            rw [H7] at H4
            simp at H4
            rw [H4, pow_add] at H1
            obtain ⟨d, H1⟩ := H1
            simp at H1
            rw [mul_assoc] at H1
            omega
        . subst k1
          obtain H6 | H6 | H6 := H6
          . subst k2
            tauto
          . subst k2
            tauto
          . have H7: k2 = 2 + (k2 - 2) := by omega
            rw [H7] at H4
            simp at H4
            rw [H4, pow_add] at H1
            obtain ⟨d, H1⟩ := H1
            simp at H1
            repeat rw [mul_assoc] at H1
            omega
        . subst k1
          obtain H6 | H6 | H6 := H6
          . subst k2
            tauto
          . subst k2
            tauto
          . have H7: k2 = 2 + (k2 - 2) := by omega
            rw [H7] at H4
            simp at H4
            rw [H4, pow_add] at H1
            obtain ⟨d, H1⟩ := H1
            simp at H1
            repeat rw [mul_assoc] at H1
            omega
        . have H7: k1 = 3 + (k1 - 3) := by omega
          rw [H7] at H4
          rw [H4, pow_add] at H1
          obtain ⟨d, H1⟩ := H1
          simp at H1
          repeat rw [mul_assoc] at H1
          omega

      . -- here it is easy - we just looks at all possible values for `x`
        -- (from `H1`) and check that they divide `1996`
        simp at H1
        obtain H1 | H1 | H1 | H1 | H1 | H1 := H1 <;> subst x <;> norm_num

    rw [H0]
    rfl