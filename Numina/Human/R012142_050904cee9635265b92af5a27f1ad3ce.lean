import Mathlib

/- 11.40 Let the natural number $n$ be a multiple of 17, and in its binary representation, it has exactly three digits that are 1. Prove that the binary representation of $n$ has at least six digits that are 0, and if it has exactly seven digits that are 0, then $n$ is even.
(British Mathematical Olympiad, 1982) -/
theorem number_theory_186505 {n : ℕ} (hn : 17 ∣ n)
    (h : (Nat.digits 2 n).count 1 = 3) :
    6 ≤ (Nat.digits 2 n).count 0 ∧ ((Nat.digits 2 n).count 0 = 7 → Even n) := by

  -- the first auxiliary lemma:
  -- no digits that are `1` iff the number is `0`
  have aux (m: ℕ): (Nat.digits 2 m).count 1 = 0 ↔ m = 0 := by
    constructor <;> intro H
    . -- we use strong induction on the variable `m`
      induction m using Nat.strong_induction_on with | h m iH =>
      -- either `m` is zero, or it is nonzero
      -- first case is, of course, very easy
      have H0: m = 0 ∨ 0 < m := by omega
      obtain H0 | H0 := H0
      . exact H0
      . -- we use a library lemma that expresses `Nat.digits 2 m` using `m / 2` and `m % 2`
        -- that's good because the `m / 2` is less than `m`
        -- and we can use the induction hypothesis `iH`
        rw [Nat.digits_of_two_le_of_pos (by simp) H0] at H
        -- simplify the expression again by using a library lemma
        rw [List.count_cons] at H
        -- now we simplify in the hypothesis `H`
        -- which removes the `if` part of this hypothesis
        -- because in the case that `(m % 2 == 1) = true` the expression becomes
        -- long expression + 1 = 0, which is simplified to `False`
        simp at H
        -- now the hypothesis `H` has become a conjunction, which we destruct
        obtain ⟨H1, H2⟩ := H
        -- obvious step is to apply induction hypothesis `iH` on the `H1`
        apply iH (m / 2) (by omega) at H1
        -- now `omega` solves the goal, because the only way for
        -- even number (see `H2`) to be zero when divided by `2`,
        -- is to be zero
        omega
    . -- this direction is easy, just substitue value `m = 0` everywhere and simplify
      subst m
      simp

  -- the second auxiliary lemma:
  -- if the number of digits `1` in the binary expansion of number `n` is
  -- equal to `k + 1`, then there's some natural numbers `mm` and `p`
  -- that satisfy an expression (seen in statement of the lamma, left side of conjunction)
  -- and also the binary expansion of `mm` contains one less digit `1` than `m`
  have aux0 (m k: ℕ) (Hm: (Nat.digits 2 m).count 1 = k + 1):
      ∃ (mm p: ℕ), m = 2 ^ p * (1 + 2 * mm) ∧ (Nat.digits 2 mm).count 1 = k := by
    -- we again use the strong induction on the variable `m`
    induction m using Nat.strong_induction_on with | h m iH =>
    -- two cases: `m` is zero or `m` is nonzero natural number
    have H: m = 0 ∨ 0 < m := by omega
    -- we take a look at both possibilities
    obtain H | H := H
    . -- first one is easy - substitute and simplify
      subst m
      simp at *
    . -- we again use both library lemmas we used in the proof
      -- of the previous lemmma `aux`:
      -- the first expresses `Nat.digits 2 m` in the terms of
      -- `Nat.digits 2 (m / 2)` and `m % 2`, and the second simplifies a bit
      rw [Nat.digits_of_two_le_of_pos (by norm_num) H] at Hm
      rw [List.count_cons] at Hm
      -- now we have to split `if`s in hypothesis `Hm` and look at both possibilities
      split_ifs at Hm <;> rename_i H0
      . -- the first possibility - with `(m % 2 == 1) = true`
        -- in this case the last binary digit of `m` was `1`,
        -- we have found it and the `mm` is `m / 2` and `p` is `0`
        use (m / 2), 0
        -- simplify, destruct the goal and, in one case, use the tactic `omega`
        -- in other just use the hypothesis that's exactly the same as the goal
        simp at Hm H0 ⊢
        constructor
        . omega
        . exact Hm
      . -- the second possibility - with `¬ (m % 2 == 1) = false`
        -- in this case the last binary digit of `m` was `0`, so we chop it off
        -- and continue to search for digit `1`
        -- in the remaining part of the number (`m / 2`).
        -- at first we simplify a bit (to make the hypothesis `Hm` good for
        -- applying the induction hypothesis `iH`), then we do that (use `iH` on `Hm`)
        simp at Hm
        apply iH at Hm
        . -- after applying `iH` on `Hm`, the hypothesis `Hm` becomes a nice
          -- statement about existence of things, that can be nicely destructed
          obtain ⟨m', p, H1, H2⟩ := Hm
          -- and then we use variables we got in the proof of existence in the goal
          use m', p + 1
          refine ⟨?_, H2⟩
          -- we rewrite in the part `2 ^ (p + 1)`, mostly because the `omega`
          -- don't understand exponents well
          rw [Nat.pow_add]
          -- we simplify at `H0` (important for `omega`) and at the goal
          simp at H0 ⊢
          -- useful tiny result
          have H3: m = 2 * (m / 2) := by omega
          -- now some rewrites and then tactic `ring` solves the goal
          rw [H3, H1]
          ring
        . -- this goal has appeared because it was necessary for
          -- using the induction hypothesis `iH`.
          -- in short, from the previously proven lemma `aux` we know that `m` isn't zero.
          -- we prove that, then use final `omega` to close the goal
          have H0: ¬ List.count 1 (Nat.digits 2 (m / 2)) = 0 := by omega
          rw [aux] at H0
          omega

  -- the third auxiliary lemma:
  -- if we look at the binary expansion of the number,
  -- count the number of zeroes, then count the number of ones,
  -- and then add both results together, we get the total number of binary digits
  have aux1 (m: ℕ): (Nat.digits 2 m).count 0 + (Nat.digits 2 m).count 1 = (Nat.digits 2 m).length := by
    -- strong induction again
    induction m using Nat.strong_induction_on with | h m iH =>
    -- two cases: either `m` is zero, or it is nonzero number
    -- the first case is easy
    have H: m = 0 ∨ 0 < m := by omega
    obtain H | H := H
    . subst m
      simp
    . -- we rewrite using the two useful lemmas
      rw [Nat.digits_of_two_le_of_pos (by norm_num) H]
      rw [List.count_cons, List.count_cons]
      -- now we have `if`s to split, also
      -- we do simplifications in all four cases
      split_ifs <;> rename_i H0 H1 <;> simp at H0 H1
      . -- first case is solved by `omega`, because there's a contradiction
        omega
      . -- rewrite, simplify, rewrite using the induction hypothesis `iH`
        -- finish by using tactic `ring`
        rw [H0]
        simp
        rw [<- iH (m / 2) (by omega)]
        ring
      . -- the same approach as in the previous case
        rw [H0]
        simp
        rw [<- iH (m / 2) (by omega)]
        ring
      . -- in the last case there's again a contradiction
        omega

  -- the fourth auxiliary lemma:
  -- given upper bound on number of binary digits,
  -- we get an useful upper bound on the number itself
  have aux2 (m a: ℕ): (Nat.digits 2 m).length ≤ a → m < 2 ^ a := by
    intros H
    have H1 := Nat.lt_base_pow_length_digits (b:=2) (m:=m) (by simp)
    have H2: 2 ^ (Nat.digits 2 m).length ≤ 2 ^ a := by
      rw [<- pow_le_pow_iff_right₀ (a := 2) (by norm_num)] at H
      omega
    omega

  -- the fifth auxiliary lemma:
  -- given lower bound on number of binary digits,
  -- we get an useful lower bound on the number itself
  have aux3 (m a: ℕ) (Hm: m ≠ 0): a ≤ (Nat.digits 2 m).length → 2 ^ (a - 1) ≤ m := by
    intro H
    have H0 := Nat.base_pow_length_digits_le 2 m (by norm_num) Hm
    have H1: a = 0 ∨ 0 < a := by omega
    obtain H1 | H1 := H1
    . subst a
      simp
      omega
    . rw [<- pow_le_pow_iff_right₀ (a := 2) (by norm_num)] at H
      have H2: 2 ^ a ≤ 2 * m := by omega
      rw [show a = (a - 1) + 1 by omega] at H2
      rw [Nat.pow_add] at H2
      omega


  -- now we start the actual proof finally!
  -- as we know, the number of ones in the binary expansion of `n` is equal to `3`.
  -- that means that the `n` can be expressed as the sum of three powers of `2`
  have number_as_sum_of_powers: ∃ k l m, k < l ∧ l < m ∧ n = 2 ^ k + 2 ^ l + 2 ^ m := by
    apply aux0 at h
    obtain ⟨n0, k, H, H0⟩ := h
    apply aux0 at H0
    obtain ⟨n1, l, H1, H2⟩ := H0
    apply aux0 at H2
    obtain ⟨n2, m, H3, H4⟩ := H2
    -- now we have used three times the lemma `aux0`
    -- next we prove that `n2` is equal to zero.
    -- how do we know that? it doesn't contains ones in its binary expansion (see `H4`).
    have H5: n2 = 0 := by
      rw [aux] at H4
      exact H4
    -- substitutions and the tactic `ring_nf` on hypothesis `H`
    subst n2 n1 n0
    ring_nf at H
    -- we use specific values to prove the statement about existence
    -- then we got conjunction of three statements,
    -- each to be proven easily
    use k, k + l + 1, k + l + m + 2
    refine ⟨?_, ?_, ?_⟩
    . omega
    . omega
    . rw [H]
      ring

  -- let's destruct this nice statement about existence
  obtain ⟨k, l, m, H, H0, H1⟩ := number_as_sum_of_powers

  constructor

  . -- we have to prove that there's at least `6` zeroes
    -- in the binary expansion of the number `n`.
    -- we do that by assuming negation of the goal and reaching some contradiction
    by_contra H2
    simp at H2

    -- auxiliary lemma about maximum value of the exponent `m`
    have max_value_of_m: m ≤ 7 := by
      -- first we prove that the total number of binary digits of `n` is at most `8`
      have H3: (Nat.digits 2 n).count 0 + (Nat.digits 2 n).count 1 ≤ 8 := by omega
      rw [aux1] at H3
      -- according to the lemma `aux2`, that means that the number `n` is less than `2 ^ 8`
      apply aux2 at H3
      -- or, the sum of the three powers of `2` is less than `2 ^ 8`
      rw [H1] at H3
      -- now we assume negation of the goal, and try to prove that there's a contradiction
      -- (this was, probably, the easiest way to solve the goal)
      by_contra H4
      -- from `H4` it follows (by `omega`) that `m` is equal to `8 + (m - 8)`
      -- (the subtraction in natural numbers stops at zero, so
      -- it isn't always true as it would be with integer numbers)
      have H5: m = 8 + (m - 8) := by omega
      -- rewrites and simplifications
      rw [H5] at H3
      rw [Nat.pow_add] at H3
      simp at H3
      -- for some reason `omega` has difficulties, when there're some exponents
      -- and I need to prove that all powers of `2` is at least `1`
      have H6: 1 ≤ 2 ^ (m - 8) := Nat.one_le_two_pow
      have H7: 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have H8: 1 ≤ 2 ^ l := Nat.one_le_two_pow
      omega

    -- now we finish this part of the proof, by looking at all possible values
    -- of `m`, `l` and `k` and then bashing them with the tactic `omega`
    interval_cases m <;> interval_cases l <;> interval_cases k <;> omega

  . -- in this part we have to prove:
    -- if number of zeroes in the binary expansion of the number `n`
    -- is equal to `7`, then this number is even number
    intros H2
    -- again we assume negation of the goal and try to prove `False`
    by_contra H3
    simp at H3

    -- now we will prove that the number `m` is equal to `9`
    have H4: m = 9 := by
      -- at first we prove that the number of binary digits
      -- of the binary expansion of `n` is precisely `10`
      have H5: (Nat.digits 2 n).count 0 + (Nat.digits 2 n).count 1 = (Nat.digits 2 n).length :=
        aux1 n
      rw [h, H2] at H5
      simp at H5

      -- the following three statements will be useful for `omega`,
      -- to work around its problems with exponents
      have Hk: 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have Hl: 1 ≤ 2 ^ l := Nat.one_le_two_pow
      have Hm: 1 ≤ 2 ^ m := Nat.one_le_two_pow
      -- our strategy - assume that `m` is not equal to `9` and prove `False`
      by_contra H8
      -- two cases: either `m` is at most `8`, or it is at least `10`
      have H9: m ≤ 8 ∨ 10 ≤ m := by omega
      obtain H9 | H9 := H9
      . -- we prove lower bound for number `n`, which it can't reach,
        -- because exponent `m` is too low
        have H6: 10 ≤ (Nat.digits 2 n).length := by omega
        apply aux3 _ _ (by omega) at H6
        -- we estimate `l` and `k` (they are definitely less than `m`)
        have H10: l + 1 ≤ m := by omega
        have H11: k + 2 ≤ m := by omega
        -- from this we get the upper bounds on summands `2 ^ m`, `2 ^ l` and `2 ^ k`
        rw [<- pow_le_pow_iff_right₀ (a := 2) (by simp)] at H10
        rw [<- pow_le_pow_iff_right₀ (a := 2) (by simp)] at H11
        rw [<- pow_le_pow_iff_right₀ (a := 2) (by simp)] at H9
        rw [Nat.pow_add] at H10
        rw [Nat.pow_add] at H11
        -- the sum is too low for the lower bound of `n` at `H6`
        omega
      . -- now we prove upper bound for the number `n`,
        -- which it is forced to "overstep", because `m` is too big
        have H6: (Nat.digits 2 n).length ≤ 10 := by omega
        apply aux2 at H6
        rw [<- pow_le_pow_iff_right₀ (a := 2) (by simp)] at H9
        omega

    -- we also prove that `k` is equal to zero
    have H5: k = 0 := by
      -- let's assume negation of the goal and prove `False`
      by_contra H5
      -- `k` is at least `1`, therefore also `l` and `m` is at least `1`
      have Hk: k = (k - 1) + 1 := by omega
      have Hl: l = (l - 1) + 1 := by omega
      have Hm: m = (m - 1) + 1 := by omega
      rw [Hk, Hl, Hm, Nat.pow_add, Nat.pow_add, Nat.pow_add] at H1
      simp at H1
      -- all summands in the hypothesis `H1` are even, therefore `n` is even number.
      -- together with the hypothesis `H3` (which states that `n` is odd number)
      -- we get a nice contradiction
      obtain ⟨d, Hd⟩ := H3
      omega

    -- and the final step: we substitute the values of `m` and `k` everywhere,
    -- then look at all possible values of `l` and solve the goal using tactic `omega`
    subst m k
    interval_cases l <;> omega