import Mathlib

/- 13th Irish 2000 Problem B4 Show that in any set of 10 consecutive integers there is one which is relatively prime to each of the others. -/
theorem number_theory_147799 (n : ℤ) :
    ∃ m ∈ Finset.Icc n (n + 9), ∀ k ∈ Finset.Icc n (n + 9), m ≠ k → IsCoprime m k := by

  -- let's start by proving useful lemma which gives to statement that two integers aren't comprimes
  have not_IsCoprime_alternative (a b: ℤ): (¬ IsCoprime a b) ↔ (∃ (d: ℤ), 1 < d ∧ d ∣ a ∧ d ∣ b) := by
    -- first, replace `IsCoprime a b` with `a.gcd b = 1`
    rw [Int.isCoprime_iff_gcd_eq_one]
    -- split double implications in two parts
    constructor <;> intro H
    . -- direction left-to-right
      -- it happens so that `Int.gcd` is defined in terms of natural numbers, using `Nat.gcd`
      -- we unfold definition of `Int.gcd` and replace `Nat.gcd` with a nicer definition
      -- using `Nat.Prime.not_coprime_iff_dvd`
      simp only [Int.gcd] at H;
      simp only [Nat.Prime.not_coprime_iff_dvd] at H
      -- one can see that hypotheses `H` and goal is very similar right now
      -- let's get the value of `p` from `H` and use it on goal
      obtain ⟨p, H0, H1, H2⟩ := H
      -- to use `p` on this goal, it must be converted to `ℤ`
      use (p: ℤ)
      -- split goal into three parts
      refine ⟨?_, ?_, ?_⟩
      . -- first lemma `Nat.one_lt_cast` is used, transforming the goal into inequality in `N`
        -- then the fact that all primes (in natural numbers) is bigger than 1 solves the goal
        simp only [Nat.one_lt_cast]
        exact Nat.Prime.one_lt H0
      . -- here we use `zify` tactic on hypothesis `H1`; `p ∣ a.natAbs` becomes `↑p ∣ |a|`
        -- if `↑p` divides absolute value of `a`, then if divides `a` itself too
        -- after rwwriting with the corresponding lemma, hypotheses `H1` becomes equal to the goal
        zify at H1
        rw [dvd_abs] at H1
        exact H1
      . -- the same approach, but this time with `zify` tactic on `H2` etc.
        zify at H2
        rw [dvd_abs] at H2
        exact H2
    . -- direction right-to-left
      -- destruct hypothesis `H` into parts
      obtain ⟨d, H0, H1, H2⟩ := H
      -- intro `a.gcd b = 1`, changing goal to `False`;
      -- one will need to reach contradiction to prove this goal
      intro H3
      -- destruct hypotheses `H1` and `H2`
      obtain ⟨a', H1⟩ := H1
      obtain ⟨b', H2⟩ := H2
      -- substitue `a` and `b` everywhere
      subst a b
      -- common multiplier in parameters of `Int.gcd` is moved out of it
      -- we get the product that's equal to one
      -- that means both factors are equal to 1 or -1
      rw [Int.gcd_mul_left, mul_eq_one] at H3
      -- One hypothesis says `1 < d`, another (first part of `H3`) instead `d.natAbs = 1`
      -- this is obvious contradiction and `omega` tactic solves th goal.
      omega

  -- if integer isn't divided by 2, 3, 5, 7, then it avoids all divisors from 2 to 9 (inclusive)
  have auxiliary_lemma_about_divisors (a: ℤ) (H0: ¬ 2 ∣ a) (H1: ¬ 3 ∣ a) (H2: ¬ 5 ∣ a) (H3: ¬ 7 ∣ a):
      ∀ d ∈ Finset.Icc 2 9, d ∣ a → False := by
    intros d Hd Hda
    -- simplify the interval notation `Icc` at hypothesis `Hd` into the form of two inequalities
    -- then destruct the `Hd` into two separate inequalities
    -- it's necessary for the tactic `interval_cases d` to work
    simp only [Finset.mem_Icc] at Hd
    obtain ⟨Hd1, Hd2⟩ := Hd
    -- from `2 ≤ d` and `d ≤ 9` we get all the cases - d = 2, d = 3, d = 4, ..., d = 9
    -- with automatic substition in each case of the value of `d` everywhere
    interval_cases d
    . -- obvious contadiction (see `H0` and `Hda`), goal is solved by `contradiction` tactic,
      -- which is useful for such obvios contradiction (with hypotheses `P` and `not P`)
      contradiction
    . -- contradiction (`H1` abd `Hda`)
      contradiction
    . -- is integer is divided by 4, then it's divided by 2 too,
      -- and that contradicts hypothesis `H0`
      -- the tactic `omega` uses this contradiction to solve the goak
      omega
    . -- contradiction (`H2` and `Hda`)
      contradiction
    . -- from `6 ∣ a` follows `2 ∣ a` and that contradicts hypothesis `H0`
      omega
    . -- contradiction (`H3` and `Hda`)
      contradiction
    . -- from `8 ∣ a` follows `2 ∣ a` and that contradicts `H0`
      omega
    . -- feom `9 ∣ a` follows `3 ∣ a` and that contradicts `H1`
      omega

  -- important result: if integer `a` is from the interval `Icc n (n + 9)` and
  -- it isn't divided by any of the numbers 2, 3, 5, 7, then
  -- it is the necessary number from this interval we are searching for!
  -- it is coprime with any other number from the interval `Icc n (n + 9)`
  have sufficient_condition (m: ℤ) (Hm: m ∈ Finset.Icc n (n + 9))
      (H0: ¬ 2 ∣ m) (H1: ¬ 3 ∣ m) (H2: ¬ 5 ∣ m) (H3: ¬ 7 ∣ m):
      ∀ k ∈ Finset.Icc n (n + 9), m ≠ k → IsCoprime m k := by
    intros k Hk Hmk
    -- using the previously proven auxiliary lemma
    have H4 := auxiliary_lemma_about_divisors m H0 H1 H2 H3
    -- let's suppose that `IsCoprime m k` is false and reach contradiction
    -- that will prove that `IsCoprime m k` is true statamenet
    by_contra H5
    -- as sson as we get `¬ IsCoprime m k`, we replace with more useful alternative
    rw [not_IsCoprime_alternative] at H5
    -- let's destruct the hypothesis `H5`
    obtain ⟨d, Hd1, Hd2, Hd3⟩ := H5
    -- now there're two options - either common divisor `d` of `m` and `k`
    -- is less than 10, or at least 10
    obtain H5 | H5 := Int.lt_or_le d 10
    . -- if `d < 10`, we get contradiction using `H4`
      exact (H4 d (by simp; omega) Hd2)
    . -- the case `10 ≤ d` takes a bit longer
      -- first we destruct hypotheses `Hd2` and `Hd3`
      obtain ⟨d1, Hd2⟩ := Hd2
      obtain ⟨d2, Hd3⟩ := Hd3
      -- substiture `m` and `k` everywhere
      subst m k
      -- simplify hypothesis `Hmk`
      simp only [ne_eq, mul_eq_mul_left_iff, not_or] at Hmk
      -- now it's conjunction, which we destruct; then we simplify at `Hm` and `Hk`
      obtain ⟨H7, H8⟩ := Hmk
      simp only [Finset.mem_Icc] at Hm Hk
      -- as `d1` and `d2` aren't equal, either it is `d1 < d2` or `d2 < d1`.
      -- In both cases `linarith` solves the goal.
      -- (`d` is to big for both `d * d1` and `d * d2` to stay in the same interval `Icd n (n + 9)`)
      obtain H9 | H9 := Int.ne_iff_lt_or_gt.mp H7
      . nlinarith
      . nlinarith

  -- the plan is to prove that at least one value from the interval `Icc n (n + 9)` is good
  -- (in other words, it fulfills the sufficient condition from lemma `sufficient_condition`)

  -- let's collect all odd numbers from the interval `Icc n (n + 9)`
  -- we are not interested in even numbers, as they aren't useful for our goal
  set odd_numbers: Finset ℤ := (Finset.Icc n (n + 9)).filter (fun x => ¬ 2 ∣ x)

  -- the proof that all elements of the finset `odd_numbers` are odd
  have odd_numbers_are_odd (x: ℤ) (Hx: x ∈ odd_numbers): ¬ 2 ∣ x := by
    intro H2
    simp only [odd_numbers, Finset.mem_filter] at Hx
    tauto

  -- let's find the smallest element of `odd_numbers` and express all the finset by it
  have specific_odd_numbers: ∃ (i: ℤ), (¬ 2 ∣ i) ∧ odd_numbers = {i, i + 2, i + 4, i + 6, i + 8} := by
    -- `n` is either even number, or odd number
    obtain H4 | H4 := em (2 ∣ n)
    . -- in the first case we use `n + 1` and then simplify until `omega` works
      use (n + 1)
      constructor
      . omega
      . simp only [odd_numbers]
        ext x
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
        omega
    . -- in the second case we use `n` and do the same.
      use n
      constructor
      . omega
      . simp only [odd_numbers]
        ext x
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
        omega

  -- simple proof that there are exactly five odd numbers
  have odd_numbers_are_five: odd_numbers.card = 5 := by
    obtain ⟨x, H, H0⟩ := specific_odd_numbers
    simp [H0]

  -- next steps will be:
  -- 1) remove from the finset `odd_numbers` everything that's divided by 3;
  -- 2) or by 5
  -- 3) or by 7
  -- 4) and then prove that at least one odd number stil stays

  -- so, the first step - to remove all odd numbers that are divided by 3
  -- there are at most 2 such numbers
  have multiples_of_three_card: (odd_numbers.filter (fun x => 3 ∣ x)).card ≤ 2 := by
    obtain ⟨x0, H, H0⟩ := specific_odd_numbers
    rw [H0]
    -- there are three possible values of `x0 % 3`; we look at each case
    -- in each cases there are different options of which values will be divided by 3
    -- in each case we use extensionality, simplify and use omega
    -- in each case we prove this result about cardinality, in the end
    have H1: x0 % 3 = 0 ∨ x0 % 3 = 1 ∨ x0 % 3 = 2 := by omega
    obtain H1 | H1 | H1 := H1
    . have H2: Finset.filter (fun x => 3 ∣ x) {x0, x0 + 2, x0 + 4, x0 + 6, x0 + 8} = {x0, x0 + 6} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [H2]; simp
    . have H2: Finset.filter (fun x => 3 ∣ x) {x0, x0 + 2, x0 + 4, x0 + 6, x0 + 8} = {x0 + 2, x0 + 8} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [H2]; simp
    . have H2: Finset.filter (fun x => 3 ∣ x) {x0, x0 + 2, x0 + 4, x0 + 6, x0 + 8} = {x0 + 4} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [H2]; simp

  -- cardinality of the set of candidate values that are left after removing those divided by 3
  have card_after_step_1: 3 ≤ (odd_numbers.filter (fun x => ¬ 3 ∣ x)).card := by
    have H6: odd_numbers.card - (odd_numbers.filter (fun x => 3 ∣ x)).card ≤
             (odd_numbers.filter (fun x => ¬ 3 ∣ x)).card := by
      rw [Finset.filter_not]
      apply Finset.le_card_sdiff
    omega

  -- the same process as in the case of numbers that were divided by 3
  -- in this case there are exactly one odd number that's divided by 5
  have multiples_of_five_card: (odd_numbers.filter (fun x => 5 ∣ x)).card = 1 := by
    obtain ⟨x0, H, H0⟩ := specific_odd_numbers
    rw [H0]
    -- this time we look at 5 different cases
    have H1: x0 % 5 = 0 ∨ x0 % 5 = 1 ∨ x0 % 5 = 2 ∨ x0 % 5 = 3 ∨ x0 % 5 = 4 := by omega
    obtain H1 | H1 | H1 | H1 | H1 := H1
    . have H2: Finset.filter (fun x => 5 ∣ x) {x0, x0 + 2, x0 + 4, x0 + 6, x0 + 8} = {x0} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [H2]; simp
    . have H2: Finset.filter (fun x => 5 ∣ x) {x0, x0 + 2, x0 + 4, x0 + 6, x0 + 8} = {x0 + 4} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [H2]; simp
    . have H2: Finset.filter (fun x => 5 ∣ x) {x0, x0 + 2, x0 + 4, x0 + 6, x0 + 8} = {x0 + 8} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [H2]; simp
    . have H2: Finset.filter (fun x => 5 ∣ x) {x0, x0 + 2, x0 + 4, x0 + 6, x0 + 8} = {x0 + 2} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [H2]; simp
    . have H2: Finset.filter (fun x => 5 ∣ x) {x0, x0 + 2, x0 + 4, x0 + 6, x0 + 8} = {x0 + 6} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [H2]; simp

  -- cardinality of the set of candidate values that are left after removing those divided by 3 and 5
  have card_after_step_2: 2 ≤ (odd_numbers.filter (fun x => ¬ 3 ∣ x ∧ ¬ 5 ∣ x)).card := by
    have H: (odd_numbers.filter (fun x => ¬ 3 ∣ x)).card -
            (odd_numbers.filter (fun x => 5 ∣ x)).card ≤
            (odd_numbers.filter (fun x => ¬ 3 ∣ x ∧ ¬ 5 ∣ x)).card := by
      rw [Finset.filter_and_not]
      apply Finset.le_card_sdiff
    omega

  -- the same process as in the case of numbers that were divided by 3 or divided by 5
  -- in this case there is at most one odd number that's divided by 7

  have H8: (odd_numbers.filter (fun x => 7 ∣ x)).card ≤ 1 := by
    obtain ⟨x0, H, H0⟩ := specific_odd_numbers
    rw [H0]
    -- seven different cases
    have H1: x0 % 7 = 0 ∨ x0 % 7 = 1 ∨ x0 % 7 = 2 ∨ x0 % 7 = 3 ∨ x0 % 7 = 4 ∨ x0 % 7 = 5 ∨ x0 % 7 = 6 := by omega
    obtain H1 | H1 | H1 | H1 | H1 | H1 | H1 := H1
    . have H2: Finset.filter (fun x => 7 ∣ x) {x0, x0 + 2, x0 + 4, x0 + 6, x0 + 8} = {x0} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [H2]; simp
    . have H2: Finset.filter (fun x => 7 ∣ x) {x0, x0 + 2, x0 + 4, x0 + 6, x0 + 8} = {x0 + 6} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [H2]; simp
    . have H2: Finset.filter (fun x => 7 ∣ x) {x0, x0 + 2, x0 + 4, x0 + 6, x0 + 8} = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton];
        simp only [Finset.not_mem_empty, iff_false, not_and]
        omega
      rw [H2]; simp
    . have H2: Finset.filter (fun x => 7 ∣ x) {x0, x0 + 2, x0 + 4, x0 + 6, x0 + 8} = {x0 + 4} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [H2]; simp
    . have H2: Finset.filter (fun x => 7 ∣ x) {x0, x0 + 2, x0 + 4, x0 + 6, x0 + 8} = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        simp only [Finset.not_mem_empty, iff_false, not_and]
        omega
      rw [H2]; simp
    . have H2: Finset.filter (fun x => 7 ∣ x) {x0, x0 + 2, x0 + 4, x0 + 6, x0 + 8} = {x0 + 2} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [H2]; simp
    . have H2: Finset.filter (fun x => 7 ∣ x) {x0, x0 + 2, x0 + 4, x0 + 6, x0 + 8} = {x0 + 8} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [H2]; simp

  -- cardinality of the set of remaining candidate values is at least 1
  have card_after_step_3: 1 ≤ (odd_numbers.filter (fun x => ¬ 3 ∣ x ∧ ¬ 5 ∣ x ∧ ¬ 7 ∣ x)).card := by
    have H: (odd_numbers.filter (fun x => ¬ 3 ∣ x ∧ ¬ 5 ∣ x)).card -
            (odd_numbers.filter (fun x => 7 ∣ x)).card ≤
            (odd_numbers.filter (fun x => ¬ 3 ∣ x ∧ ¬ 5 ∣ x ∧ ¬ 7 ∣ x)).card := by
      simp_rw [<- and_assoc]
      nth_rw 2 [Finset.filter_and_not]
      apply Finset.le_card_sdiff
    omega

  -- and now the final part of the proof
  simp_rw [Finset.one_le_card, Finset.filter_nonempty_iff] at card_after_step_3
  obtain ⟨m, Hm, H, H0, H1⟩ := card_after_step_3
  use m
  constructor
  . simp only [odd_numbers, Finset.mem_filter, Finset.mem_Icc] at Hm
    simp only [Finset.mem_Icc]
    exact Hm.1
  . intro k Hk Hmk
    exact (sufficient_condition m (by simp [odd_numbers] at Hm; simp; exact Hm.1)
           (by simp [odd_numbers] at Hm; omega) H H0 H1 k Hk Hmk)
 
  --- QED