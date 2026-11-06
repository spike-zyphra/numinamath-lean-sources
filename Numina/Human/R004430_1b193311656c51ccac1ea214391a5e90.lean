import Mathlib

open Finset

-- an useful lemma for this proof:
-- the sum on the left side multiplies
-- each natural number from the interval by `2`
-- and then adds them together
lemma Gauss_formula_but_for_interval (a b: ℕ) (Hab: a ≤ b):
    ∑ i ∈ Icc a b, (2 * i) = (b - a + 1) * (a + b) := by
  have H: Icc a b = Ico (0 + a) ((b - a + 1) + a) := by
    ext x
    simp
    omega
  -- first we rewrite using `H` to prepare the sum it
  -- for the library lemma that shifts the index of summation
  -- and moves the summation interval in the opposite direction
  rw [H, <- Finset.sum_Ico_add]
  -- some simplifications
  rw [<- mul_sum, mul_comm, sum_add_distrib, Nat.add_mul]
  -- we convert the `Ico 0 (b - a + 1)` to the corresponding `Finset.range`
  -- to use the library lemma with formula for this kind of sum
  rw [Nat.Ico_zero_eq_range, sum_range_id_mul_two]
  -- simp removes the last sum sign
  -- (sum of function that's constant over the finite interval
  -- is equal to this constant multiplied by length of the interval)
  simp
  -- tiny arithmetic manipulation to prepare for use of library lemma
  rw [show (b - a + 1) * a * 2 = (b - a + 1) * (2 * a) by ring]
  rw [<- Nat.mul_add]
  -- we remove the common multiplicand from the equality we are proving
  congr 1
  -- and this is solved by `omega`
  omega


/- 4. Let l(n) denote the greatest odd divisor of the number n. Determine the value of the sum


$$

l(1)+l(2)+l(3)+\ldots+l\left(2^{2013}\right) .

$$
 -/
theorem number_theory_265551 {f : ℕ → ℕ} (hf : ∀ n, f n = sSup {x | Odd x ∧ x ∣ n}) :
    ∑ i ∈ Finset.Icc 1 (2 ^ 2013), f i = (4 ^ 2013 + 2) / 3 := by

  -- we define a helper function
  let g: ℕ → ℕ := fun k =>
    match k with
    | 0 => f 1
    | k' + 1 => ∑ i ∈ Finset.Icc (2 ^ k' + 1) (2 ^ (k' + 1)), f i

  -- we prove this set equality
  -- which is useful proving equality `f (2 * n) = f n`
  have set_for_2n (n: ℕ): {x | Odd x ∧ x ∣ (2 * n)} = {x | Odd x ∧ x ∣ n} := by
    -- as usual, we use set extensionality
    ext x
    constructor <;> intro H
    . -- direction forwards
      simp at *
      obtain ⟨H, H0⟩ := H
      constructor
      . exact H
      . -- we need to prove that any odd `x` that divides `2 * n` aldo divides `n`
        -- at first we "destruct" hypothesis `H0`
        -- to get  `d` such that `x = 2 * d + 1`
        -- and then we look at two possible cases:
        -- `d` is even or `d` is odd
        obtain ⟨d, H0⟩ := H0
        obtain H2 | H2 := Nat.even_or_odd d
        . -- if `d` is even, we use `d / 2` for the goal
          obtain ⟨d1, H2⟩ := H2
          use d1
          nlinarith
        . -- this case is impossible (product of two odd numbers can't be even),
          -- so we will prove a contradiction
          exfalso
          -- get information out of hypotheses `H` and `H2`
          obtain ⟨d1, H⟩ := H
          obtain ⟨d2, H2⟩ := H2
          -- substitute values off `d` and `x`, simplify and
          -- prove goal by use of `omega` tactic
          subst x d
          ring_nf at H0
          omega
    . -- direction backwards is much easier to do
      simp at *
      obtain ⟨H, H0⟩ := H
      constructor
      . exact H
      . -- if `x` divides `n`, it definitely divides `2 * n` too
        exact Dvd.dvd.mul_left H0 2

  -- formula for values of the function `f` for even numbers
  have formula_for_f_of_even_number (n: ℕ): f (2 * n) = f n := by
    rw [hf, hf, set_for_2n]

  -- formula for values of the function `f` for even numbers
  have formula_for_f_of_odd_number (n: ℕ): f (2 * n + 1) = 2 * n + 1 := by
    -- rewrite the goal with `hf`,
    -- then apply library lemma that changes goal to
    -- something more usual
    rw [hf]
    apply IsLUB.csSup_eq
    . -- unfold and simplify
      unfold IsLUB IsLeast upperBounds
      simp
      constructor
      . -- first subgoal.
        -- here we use the property, that a divisor of natural number
        -- is always equal or less than the divided number
        intros a Ha Ha0
        apply Nat.divisor_le
        simp_all
      . -- second subgoal.
        unfold lowerBounds
        simp
        intros a H
        apply H
        . simp
        . simp
    . -- we also need to proved that this set is nonempty
      -- we do that by providing witness (`2 * n + 1`)
      use (2 * n + 1)
      simp

  -- first major result - we prove the formula for values of `g (n + 1)`
  have formula_for_g_n (n: ℕ): g (n + 1) = 4 ^ n := by
    induction n with
    | zero =>
      -- case for `f 1` is easy
      simp [g]
      rw [formula_for_f_of_even_number 1, formula_for_f_of_odd_number 0]
      rfl
    | succ n iH =>
      simp [g]
      -- here we will change this sum to addition of two another sums
      -- basically separating all elements into two parts
      have H (i: ℕ): f i = if Odd i then f i else f i := (ite_self (f i)).symm
      rw [sum_congr rfl (fun x a => H x)]
      rw [Finset.sum_ite]
      -- here we use argument with bijection between elements of two sums
      have H0: ∑ x ∈ filter (fun x => ¬ Odd x) (Icc (2 ^ (n + 1) + 1) (2 ^ (n + 1 + 1))), f x =
               ∑ x ∈ Icc (2 ^ n + 1) (2 ^ (n + 1)), f x := by
        apply sum_bij (fun n _ => n / 2)
        . -- the first of four subgoals that are generated by the use of the lamm
          -- we have to prove that every element from the domain of the first sum
          -- is transformed into element of the domain of the second sum
          -- by use of given function `fun n _ => n / 2` or,
          -- to put more simply - by division by `2`
          simp
          intros a H0 H1 H2
          -- we get the information from `H2` and then use `omega` tactic
          obtain ⟨d, H2⟩ := H2
          omega
        . -- we have to prove that this function is injective
          simp
          intros a H0 H1 H2 a' H3 H4 H5
          -- same idea - destruct `H2` and `H5`, allowing `omega` to solve the goal
          obtain ⟨d, H2⟩ := H2
          obtain ⟨d', H5⟩ := H5
          omega
        . simp
          intros b H0 H1
          -- here we need to provide inverse of the function
          -- we provided to the lemma `sum_bij` and to prove that
          -- it takes the number from the domain of the second sum
          -- to the domain of the first sum.
          use (2 * b)
          simp
          omega
        . -- last subgoal - to prove that the given function
          -- doesn't change the value of the element
          simp
          intros a H0 H1 H2
          obtain ⟨d, H2⟩ := H2
          subst a
          ring_nf
          simp
          rw [mul_comm]
          exact formula_for_f_of_even_number d
      -- argument with bijection between elements of sums is used on the second part too
      -- this time we provide a function, that divides number by `2` and then adds `1`.
      -- four relatively easy proofs are generated by the use of this lemma `sum_bij`
      have H1: ∑ x ∈ filter (fun x => Odd x) (Icc (2 ^ (n + 1) + 1) (2 ^ (n + 1 + 1))), f x =
               ∑ x ∈ Icc (2 ^ n + 1) (2 ^ (n + 1)), f (2 * x - 1) := by
        apply sum_bij (fun n _ => n / 2 + 1)
        . -- if the number is from domain of the first sum,
          -- the function takes it to the domain of the second sum
          simp
          intros a H1 H2 H3
          obtain ⟨d, H3⟩ := H3
          omega
        . -- proof that the function is injective
          simp
          intros a H1 H2 H3 a' H4 H5 H6 H7
          obtain ⟨d, H3⟩ := H3
          obtain ⟨d', H6⟩ := H6
          omega
        . -- proof that the function is sirjective
          simp
          intros b H1 H2
          use (2 * b - 1)
          refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
          . omega
          . omega
          . use (b - 1)
            omega
          . omega
        . -- prove that the inverse function doesn't change the value
          -- of the element of the sum
          simp
          intros a H1 H2 H3
          congr 1
          obtain ⟨d, H3⟩ := H3
          omega

      -- now we change both parts of the sum to the simpler ones,
      -- using last two results we just proved
      rw [H0, H1]; clear H0 H1
      simp [g] at iH
      -- rewrite using the induction hypothesis
      rw [iH]

      -- we also simplify the expression under the sum sign
      -- using the formula for values of function `f` for odd values
      have H2: ∑ x ∈ Icc (2 ^ n + 1) (2 ^ (n + 1)), f (2 * x - 1) = ∑ x ∈ Icc (2 ^ n + 1) (2 ^ (n + 1)), (2 * x - 1) := by
        rw [sum_congr rfl (f := fun x => f (2 * x - 1)) (g := fun x => 2 * x - 1) ?_]
        simp
        intros x H2 H3
        rw [show 2 * x - 1 = 2 * (x - 1) + 1 by omega]
        rw [formula_for_f_of_odd_number]
      rw [H2]; clear H2

      -- useful tiny result for tactic `omega` to use
      have H3: 1 ≤ 2 ^ n := Nat.one_le_two_pow

      -- we change the subtraction under sum sign
      -- to two sums that are subtracted
      rw [sum_tsub_distrib]
      . -- first we use the lemma we proved before,
        -- which calculates sum of doubled simple arithmetic progression
        rw [Gauss_formula_but_for_interval]
        . simp
          -- now many rewrites follows
          -- to prove that the left side in the equality in the goal
          -- is equal to the right side
          ring_nf
          rw [show 2 ^ n * 2 - (1 + 2 ^ n) = 2 ^ n - 1 by omega]
          rw [show 1 + (2 ^ n - 1) = 2 ^ n by omega]
          rw [tsub_mul, tsub_mul]
          rw [show 2 ^ n * 2 ^ n = (2 * 2) ^ n by exact Eq.symm (Nat.mul_pow 2 2 n)]
          norm_num
          rw [show 2 ^ n * 2 - 2 ^ n = 2 ^ n by omega]
          have H4: 2 ^ n ≤ 4 ^ n := by
            refine Nat.pow_le_pow_left (by norm_num) n
          rw [show 2 ^ n + (4 ^ n * 3 - 2 ^ n * 3) = 4 ^ n * 3 - 2 ^ n * 2 by omega]
          rw [show 4 ^ n * 3 - 2 ^ n * 2 + 2 ^ n * 3 - 2 ^ n = 4 ^ n * 3 by omega]
          ring_nf
        . -- of course, we need to prove that the interval isn't empty,
          -- or, in other words, the start value of it isn't bigger than end value
          rw [pow_add]
          simp
          omega
      . -- for each natural number `x` from the interval is true that `1 ≤ 2 * x`
        -- it's necessary condition for the lemma `sum_tsub_distrib` to work
        simp
        intros x H3 H4
        omega

  -- here we express sum `f 1 + f 2 + ... + f (2 ^ n)` using
  -- the values of function `g`
  have sum_of_g_is_sum_of_f (n: ℕ) (Hn: 1 ≤ n): f 1 + ∑ i ∈ Finset.Icc 1 n, g i = ∑ i ∈ Finset.Icc 1 (2 ^ n), f i := by
    -- induction on `n`, but starting from the value `1` (instead of zero)
    induction' n, Hn using Nat.le_induction with m hm iH
    . -- base case is easy
      simp [g]
      rfl
    . -- many rewrites to simplify and prove equality
      rw [show Icc 1 (m + 1) = Ico 1 (m + 1 + 1) by rfl]
      -- here we change the sum on the left into such form
      -- that the induction hypothesis `iH` can be used for a rewrite
      rw [sum_Ico_succ_top (by omega)]
      rw [show Ico 1 (m + 1) = Icc 1 m by rfl]
      rw [<- add_assoc, iH]
      simp [g]
      -- change two intervals of type `Icc` to type `Ico`
      rw [show Icc 1 (2 ^ m) = Ico 1 (2 ^ m + 1) by rfl]
      rw [show Icc (2 ^ m + 1) (2 ^ (m + 1)) = Ico (2 ^ m + 1) (2 ^ (m + 1) + 1) by rfl]
      -- finally we "concatenate" these two sums on the left side together
      -- and finish the proof of this result
      rw [sum_Ico_consecutive]
      . rfl
      . exact Nat.le_add_left 1 (2 ^ m)
      . rw [pow_add]
        simp

  -- in this step we prove the general formula for the sum
  -- for arbitrary `n` which is bigger than zero
  have general_formula_for_the_sum (n: ℕ) (Hn: 1 ≤ n):
      ∑ i ∈ Finset.Icc 1 (2 ^ n), f i = (4 ^ n + 2) / 3 := by
    -- first we rewrite using the lamma we just proved previously
    rw [<- sum_of_g_is_sum_of_f n Hn]
    -- we shift the interval in the sum a bit to the left
    -- and also remember to change summand to the new value
    have H: ∑ i ∈ Icc 1 n, g i = ∑ i ∈ Icc 0 (n - 1), g (i + 1) := by
      rw [show Icc 1 n = Ico 1 (n + 1) by rfl]
      rw [show Icc 0 (n - 1) = Ico 0 (n - 1 + 1) by rfl]
      rw [show n - 1 + 1 = n + 1 - 1 by omega]
      simp_rw [<- add_comm 1]
      rw [Finset.sum_Ico_add]
      simp
      ring_nf
    rw [H]
    -- now we replace the function `g` under the sum sign to the value `4 ^ i`
    -- (we proved the formula previously, that allows to do that)
    rw [sum_congr rfl (fun x a => formula_for_g_n x)]
    rw [show Icc 0 (n - 1) = Ico 0 (n - 1 + 1) by rfl]
    rw [<- Finset.range_eq_Ico]
    rw [show HPow.hPow 4 = fun x => 4 ^ x by rfl]
    -- we rewrite using the formula for sum of the geometric series
    rw [Nat.geomSum_eq (by norm_num)]
    rw [show n - 1 + 1 = n by omega]
    -- change `f 1` to `1` and simplify
    rw [formula_for_f_of_odd_number 0]
    simp
    -- now after some simplifications and use of the `omega` tactic,
    -- this result is proven
    nth_rw 1 [show 1 = 3 / 3 by rfl]
    rw [<- Nat.add_div_of_dvd_right (by simp)]
    congr 1
    have H0: 1 ≤ 4 ^ n := Nat.one_le_pow' n 3
    omega

  -- rest is easy
  apply general_formula_for_the_sum
  norm_num