import Mathlib

/- Let $p$ and $q$ be two different primes. Prove that


$$

\left\lfloor\frac{p}{q}\right\rfloor+\left\lfloor\frac{2 p}{q}\right\rfloor+\left\lfloor\frac{3 p}{q}\right\rfloor+\ldots+\left\lfloor\frac{(q-1) p}{q}\right\rfloor=\frac{1}{2}(p-1)(q-1) .

$$


(Here $\lfloor x\rfloor$ denotes the largest integer not greater than $x$.) -/
theorem number_theory_240146 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) :
    ∑ i ∈ Finset.range q, ⌊(i * p / q : ℝ)⌋ = ((p - 1) * (q - 1)) / 2 := by

  -- the plan is such:
  -- 1) first move anything from real numbers to natural numbers
  --    because they are more appropriate for this kind of problem
  --    the goal will transform to such:
  --    `∑ x ∈ Finset.range q, x * p / q = (p - 1) * (q - 1) / 2`
  -- 2) then prove formula for the `2 * ∑ i ∈ Finset.range (q + 1), (i * p) / q`
  --    because it's easier to work with
  -- 3) final step is proving formula for the `∑ i ∈ Finset.range q, (i * p) / q`

  -- let's get an equivalent expression for the left side of the goal
  have alternative_left_side:
      ∑ (i ∈ Finset.range q), ⌊(i: ℝ) * (p: ℝ) / (q: ℝ)⌋ =
      ((∑ (i ∈ Finset.range q), (i * p) / q): ℤ) := by
    -- we use tactic `congr` with following `ext i`
    -- to get rid of sum signs and move to proving equality
    -- of corresponding elements of these sums
    congr
    ext i
    -- now we prove that the expression inside `Int.floor` brackets (`⌊ ⌋`)
    -- can be replaced by similar expression where all natural numbers
    -- are first coerced to rational numbers,
    -- value of the expression calculated and only then
    -- resulting expression coerced from rational numbers to real numbers
    have H: ↑i * ↑p / ↑q = (((i: ℚ) * (p: ℚ) / (q: ℚ)): ℝ) := by
      simp only [Rat.cast_natCast]
    -- now we rewrite with `H` in the goal and then use tactic `norm_cast`,
    -- which (luckily to us) solves the goal
    rw [H]
    norm_cast

  -- replace the left side of the goal
  rw [alternative_left_side]

  -- we prove that `(p - 1) * (q - 1)` is even number
  have even_expression: 2 ∣ ((p - 1) * (q - 1)) := by
    -- two cases: either the prime `p` is equal to `2`, or it isn't
    obtain H | H := eq_or_ne p 2
    . -- replace `p` everywhere with `2` and simplify
      subst p
      simp only [Nat.add_one_sub_one, one_mul]
      -- now we have to prove that `q - 1` is even number
      -- or, in other words, that `q` is odd number.
      -- there is specific theorem for that,
      -- which uses the fact that `q` is prime that isn't equal to `2`
      have H0: Odd q := Nat.Prime.odd_of_ne_two hq hne.symm
      -- now it's easy: replace `q` with `d + d + 1`
      -- (where `d` is some natural number)
      -- and then simplify
      obtain ⟨d, Hq⟩ := H0
      subst q
      simp only [add_tsub_cancel_right, dvd_mul_right]
    . -- as `p` is prime that's not equal to `2`, then its odd number.
      -- same idea - replace `p` with `d + d + 1`
      -- (`d` is some natural number) and simplify
      have H1: Odd p := Nat.Prime.odd_of_ne_two hp H
      obtain ⟨d, Hp⟩ := H1
      subst p
      simp only [add_tsub_cancel_right, mul_assoc, dvd_mul_right]

  -- every prime number is bigger than `1`
  -- these tiny lemmas will be useful (for `omega` etc.)
  have one_lt_p: 1 < p := Nat.Prime.one_lt hp
  have one_lt_q: 1 < q := Nat.Prime.one_lt hq

  -- let's get an equivalent expression for the right side of the goal
  have alternative_right_side: ((p: ℤ) - 1) * ((q: ℤ) - 1) / 2 = ↑((p - 1) * (q - 1) / 2) := by
    -- first some simplifications that
    -- moves coercions on the right side of the current goal
    simp only [Int.ofNat_ediv, Nat.cast_mul, Nat.cast_ofNat]
    -- now we only have to prove these simple equalities,
    -- using tactic `omega`, and then rewrite by them
    have H: ↑(p - 1) = (p: ℤ) - 1 := by omega
    have H0: ↑(q - 1) = (q: ℤ) - 1 := by omega
    rw [H, H0]

  -- replace the right side of the goal
  rw [alternative_right_side]

  -- another call of tactic `norm_cast` that removes
  -- all coercions from natural numbers to integers in the goal
  norm_cast

  -- we have completed the first step of the plan

  -- every two different primes are coprimes
  have p_and_q_are_coprimes: Nat.Coprime p q := by
    rw [<- Nat.coprime_primes hp hq] at hne
    exact hne

  -- useful lemma about variables `p` and `q`
  -- which will be used further to prove another lemma
  have no_nontrivial_points_on_diagonal (i: ℕ) (H: i ∈ Finset.range (q + 1)):
      q ∣ (i * p) ↔ (i = 0 ∨ i = q) := by
    -- the goal is double implication, therefore we destruct it into two goals
    constructor <;> intro H0
    . -- if `q` divides product `i * p`, then `q` divides `i`
      -- (we are using lemma from the library and
      -- the fact that `p` and `q` are coprimes)
      apply (Nat.Coprime.dvd_of_dvd_mul_right p_and_q_are_coprimes.symm) at H0
      -- simplify hypothesis `H` to more useful form
      simp at H
      -- change `i` to `q * d` (where `d` is some natural numbers)
      -- and substitute `i` everywhere
      obtain ⟨d, Hd⟩ := H0
      subst i
      -- there are three cases: `d` is zero, `d` is one or `d` is bigger than `1`
      have H1: d = 0 ∨ d = 1 ∨ 1 < d := by omega
      obtain H1 | H1 | H1 := H1
      . -- substitute and simplify to solve the goal
        subst d
        simp
      . -- substitute and simplify to solve the goal
        subst d
        simp
      . -- hypotheses contain contradiction
        -- (`d` is too big for inequality at `H` to be true)
        -- tactic `nlinarith` solves the goal
        nlinarith
    . -- we destruct disjunction in hypothesis `H0`,
      -- subsitute value of `i` and simplify
      obtain H0 | H0 := H0
      . subst i
        simp
      . subst i
        simp

  have auxiliary_lemma (a b c: ℕ) (H: c ∣ (a + b)) (Ha: ¬ c ∣ a) (Hc: 0 < c):
      a / c + b / c + 1 = (a + b) / c := by
    -- use the following library lemma
    rw [Nat.add_div Hc]
    . -- use tactic `congr` (with depth equal to `1`)
      -- to remove common parts on the both sides of
      -- the equality that we need to prove
      congr 1
      -- get rid of conditional in the goal,
      -- getting two possibilities instead
      split_ifs <;> rename_i H0
      . -- easy
        rfl
      . -- if we could prove the statement  `c ≤ a % c + b % c`,
        -- we would succed proving the goal.
        -- we use tactic `exfalso` to replace the goal with `False`,
        -- and then `apply H0` replaces tha goal
        -- with the statement
        exfalso
        apply H0
        -- rest is done by using some specific library lemma
        exact Nat.le_mod_add_mod_of_dvd_add_of_not_dvd H Ha

  -- this is specializationn of the lemma `auxiliary_lemma`
  -- (with `a := q - i`, `b := i` and `c := q`, where `0 ≤ i ≤ q`),
  -- which will be important for proving the formula of the sum
  have important_result (i: ℕ) (Hi: i ∈ Finset.range (q + 1)):
      (q - i) * p / q + (i * p) / q + 1 =
      if (i = 0) then p + 1 else if (i = q) then p + 1 else p := by
    -- first simplify hypothesis `Hi` to more useful form
    simp at Hi
    -- intermediate result, proven by use of tactic `omega`
    have H: q - i + i = q := by
      omega
    -- let's get rid of the `if .. then .. else ..` construction
    split_ifs
    . -- substitute value of variable `i` every,
      -- then simplify and use library lemma
      subst i
      simp
      rw [Nat.mul_div_right _ (by omega)]
    . -- same approach:
      -- substitute value of variable `i` every,
      -- then simplify and use the same library lemma
      subst i
      simp
      rw [Nat.mul_div_right _ (by omega)]
    . -- now we use lemma `auxiliary_lemma` which we proved earlier
      rw [auxiliary_lemma]
      . -- some rewrites are enough to solve the goal
        rw [<- Nat.add_mul, H, Nat.mul_div_right _ (by omega)]
      . -- some rewrites and then we use variable `p` as the witness
        rw [<- Nat.add_mul, H]
        use p
      . -- rewrite using previous lemma `no_nontrivial_points_on_diagonal`,
        -- then simplify (if necessary) and use tactic `omega`
        rw [no_nontrivial_points_on_diagonal]
        . omega
        . simp
          omega
      . -- `0 < q` follows from hypothesis `one_lt_q`,
        -- which states that `1 < q`.
        -- tactic `omega` proves this obvious goal
        omega

  -- this lemma proves formula for useful sum, multiplied by `2`.
  -- this sum is easier to work, compared to the one in the goal
  have useful_formula: 2 * ∑ (i ∈ Finset.range (q + 1)), ((i * p) / q + 1) = (p + 1) * (q + 1) + 2 := by
    -- 2 * sum = sum + sum
    rw [Nat.two_mul]
    -- rewrite using library lemma on the first instance of the sum
    -- this lemma reverses the order of elements in the sum,
    -- changing the expression for the elements accordingly
    nth_rw 1 [<- Finset.sum_range_reflect]
    -- we can put everything under one sum sign,
    -- because sums has distributivity property
    rw [<- Finset.sum_add_distrib]
    -- some simplification (`q + 1 - 1` changes to simply `q`)
    simp only [add_tsub_cancel_right]
    -- now we change the expression under sum sign a bit
    -- because we will use lemma `important_result` on the goal a bit later
    simp_rw [show ∀ (i: ℕ), ((q - i) * p / q + 1 + (i * p / q + 1)) = (q - i) * p / q + i * p / q + 1 + 1 by intro i; ring]
    -- move that annoying second `+ 1` to another sum
    rw [Finset.sum_add_distrib]
    -- now we can rewrite under the first sum sign finally,
    -- using previously proven lemma 'important_result`
    rw [Finset.sum_congr (h := rfl) important_result]
    -- repeatedly use library lemma to get rid of
    -- these `if .. then .. else` constructions under the sum signs
    simp_rw [Finset.sum_ite]
    -- some simplifications
    simp only [Finset.range_filter_eq, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
      ↓reduceIte, Finset.sum_const, Finset.card_singleton, smul_eq_mul, one_mul, Finset.card_range,
      mul_one]
    -- if we keep only those elements of `Finset.range (q + 1)`
    -- that aren't equal to zero, then we get `Finset.Icc 1 q`.
    -- the proof of used equality is simple and
    -- we will use this approach twice more times
    rw [show Finset.filter (fun x => x ≠ 0) (Finset.range (q + 1)) = Finset.Icc 1 q by ext i; simp; omega]
    -- if we keep only those elements of `Finset.Icc 1 q`
    -- that are equal to `q`, then we get singleton set `{q}`
    rw [show Finset.filter (fun x => x = q) (Finset.Icc 1 q) = {q} by ext i; simp; omega]
    -- if we keep only those elements of `Finset.Icc 1 q`
    -- that aren't equal to `q`, then we get `Finset.Icc 1 (q - 1)`
    rw [show Finset.filter (fun x => x ≠ q) (Finset.Icc 1 q) = Finset.Icc 1 (q - 1) by ext i; simp; omega]
    -- a bit more simplifications
    simp only [Finset.card_singleton, one_mul, Nat.card_Icc, add_tsub_cancel_right]
    -- now the goal is relatively simple arithmetical equality
    -- which we simplify a bit with tactic `ring_nf`,
    -- then we do few rewrites
    -- and finally allow tactic `ring` to finish the goal
    ring_nf
    rw [add_assoc 3 (p * 2) (p * (q - 1)), <- Nat.mul_add]
    -- we have to get rid of that subtraction (of natural numbers),
    -- because tactic `ring` has difficulties with it
    rw [show 2 + (q - 1) = q + 1 by omega]
    ring

  -- now we do rewrites and simplifications on the lemma `useful_formula`
  -- to reach the final goal of this problem

  -- first we move from the sum over `Finset.range (q + 1)` to sum over `Finset.range q`
  rw [Finset.sum_range_succ] at useful_formula
  -- then we move that `+ 1` to outside of the sum sign
  -- because the goal is with `x * p / q` under the sum sign
  rw [Finset.sum_add_distrib] at useful_formula
  -- we get rid of that division in the hypothesis `useful_formula`
  rw [Nat.mul_div_right _ (by omega)] at useful_formula
  -- some more simplifications and rewrites
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at useful_formula
  rw [Nat.mul_add, Nat.mul_add] at useful_formula

  -- leave only the multiplied (by `2`) sum on the left side,
  -- moving everything else to the right
  have almost_done: 2 * (∑ i ∈ Finset.range q, i * p / q) = (p + 1) * (q + 1) + 2 - 2 * (p + 1) - 2 * q := by
    omega

  -- now we prove an equality for the final simplification
  -- for all numbers `a` and `b` that are bigger than zero
  have final_simplification (a b: ℕ) (Ha: 0 < a) (Hb: 0 < a): (a + 1) * (b + 1) + 2 - 2 * (a + 1) - 2 * b = (a - 1) * (b - 1) := by
    cases a with
    | zero => omega
    | succ a =>
      cases b with
      | zero => omega
      | succ b => simp; ring_nf; omega

  rw [final_simplification p q (by omega) (by omega)] at almost_done

  -- now omega finishes the goal
  -- as it knows that `(p - 1) * (q - 1)` is even number
  -- (lemma `even_expression`).
  -- it. like, does division by `2` on both sides
  -- of the equality in the lemma `almost_done`
  omega