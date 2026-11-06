import Mathlib

open Real

/- [Example 4.4.7] Let $x_{1}, x_{2}, \cdots, x_{n}$ be given real numbers. Prove that there exists a real number $x$ such that

$$

\left\{x-x_{1}\right\}+\left\{x-x_{2}\right\}+\cdots+\left\{x-x_{n}\right\} \leqslant \frac{n-1}{2} .

$$


Here the notation $\{\alpha\}$ denotes the fractional part of the real number $\alpha$, satisfying $0 \leqslant\{\alpha\}<1$. -/
theorem inequalities_208145 (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) :
    ∃ y : ℝ, ∑ i : Fin n, Int.fract (y - x i) ≤ (n - 1) / 2 := by

  -- useful lemma about sum of fractional parts of `x` and `- x`
  have fract_add_fract_neg_le_one (x: ℝ): Int.fract x + Int.fract (- x) ≤ 1 := by
    have H0 := Int.fract_add_fract_le x (-x)
    simp_all

  -- helper function, basically an abbreviation
  set f: Fin n → ℝ := fun (i: Fin n) => ∑ (k: Fin n), Int.fract (x i - x k)

  -- the first auxiliary lemma
  -- (expressing sum over `Fin n × Fin n` as sum of three different sums over `Fin n × FIn n`)
  have aux_1 (g: Fin n × Fin n → ℝ): ∑ p, g p =
        (∑ p, if p.1 = p.2 then g p else 0) +
        (∑ p, if p.1 < p.2 then g p else 0) +
        (∑ p, if p.2 < p.1 then g p  else 0) := by
      -- let's simplify right side of the goal, putting all under one sum sign
      simp [<- Finset.sum_add_distrib]
      -- using tactic `congr`, because, as we will see, expressions under sum signs are equal
      congr
      -- two functions are equal iff their values are equal for every value
      ext p
      -- now split all conditionals, solve almost every goal with `omega`
      -- and use `simp` on remaining three goals
      split_ifs <;> try omega
      . simp
      . simp
      . simp

  -- the second auxiliary lemma
  -- (it proves equality of certain sum to zero)
  have aux_2: ∑ (p: Fin n × Fin n), (if p.1 = p.2 then Int.fract (x p.1 - x p.2) else 0) = 0 := by
    -- the sum is equal to zero, because every element of it is equal to zero
    apply Finset.sum_eq_zero
    -- we have to prove that for every argument `p`, that belongs to `Finset.univ` (of `Fin n × Fin n`),
    -- the summand is equal to zero
    intro p Hp
    -- now split conditional and rest is easy
    split_ifs <;> rename_i H
    . simp only [H, sub_self, Int.fract_zero]
    . rfl

  -- the third auxiliary lemma
  -- (proves that two sums are equal)
  have aux_3 (g: Fin n × Fin n → ℝ):
      ∑ (p: Fin n × Fin n), (if p.2 < p.1 then g p else 0) =
      ∑ (p: Fin n × Fin n), (if p.1 < p.2 then g ⟨p.2, p.1⟩ else 0) := by
    -- let's change from sums over `Fin n × Fin n` to two nested sums over `Fin n`
    simp [Fintype.sum_prod_type]
    -- and use lemma that changes the order of sum signs and,
    -- of course, changes summand too correspondingly
    rw [Finset.sum_comm]

  -- the fourth auxiliary lemma
  -- (proves that certain sum conditional expression is less or equal to another one -
  -- for any value `p` of type `Fin n × Fin n`)
  have aux_4:
      ∀ p ∈ Finset.univ (α := Fin n × Fin n),
      (if p.1 < p.2 then Int.fract (x p.1 - x p.2) + (Int.fract (x p.2 - x p.1)) else (0: ℝ)) ≤
      (if p.1 < p.2 then 1 else 0) := by
    intros p Hp
    -- now split conditional
    -- in the first part we use result that we proved at the start
    -- the second is very simple and is solved by `rfl`
    split_ifs <;> rename_i H
    . have H: x p.2 - x p.1 = - (x p.1 - x p.2) := by ring
      rw [H]
      apply fract_add_fract_neg_le_one
    . rfl

  -- the fifth auxiliary lemma
  -- (proves that we get the same value in two cases:
  -- 1) when certain expression is calculated with natural numbers and then coerced to real numbers
  -- 2) when natural number is first coerced to real number and only then we calculate)
  have aux_5 (m: ℕ): @Nat.cast ℝ instNatCast (m * (m - 1) / 2) = ↑m * (↑m - 1) / 2 := by
    -- first we get rid of the case when `m = 0`,
    -- because we want to remove subtraction
    -- (it works differently for natural numbers and real numbers,
    -- if the first value is less than the second value that's subtracted)
    cases m with
    | zero =>
      norm_num
    | succ m =>
      -- simplify a bit and then look at two different possible cases:
      -- either `m` is even natural number, or `m` is odd natural number
      simp
      obtain H | H := Nat.even_or_odd m
      . -- if `m` is even natural number then it can be replaced by `d + d`,
        -- where `d` is also a natural number
        obtain ⟨d, H⟩ := H
        subst m
        simp
        -- simplify left side of the goal
        have H0: (d + d + 1) * (d + d) = ((2 * d + 1) * d) * 2 := by ring
        rw [H0, Nat.mul_div_cancel _ (by simp)]
        -- use `field_simp` which takes care of division on the right side of the goal
        -- and finish the goal with `ring`
        field_simp
        ring
      . -- same approach as in the case of even `m`
        -- if `m` is odd natural number then it can be replaced by `d + d + 1`,
        -- where `d` is also a natural number
        obtain ⟨d, H⟩ := H
        subst m
        simp
        -- simplify left side of the goal
        have H0: (2 * d + 1 + 1) * (2 * d + 1) = (d + 1) * (2 * d + 1) * 2 := by ring
        rw [H0, Nat.mul_div_cancel _ (by simp)]
        -- use `field_simp` to remove division on the right side of the goal
        -- and finish the goal with `ring`
        field_simp
        ring

  -- the sixth auxiliary lemma
  -- (proves that certain sum is equal to `↑n * (↑n - 1) / 2`)
  have aux_6: (∑ (p: Fin n × Fin n), if p.1 < p.2 then (1: ℝ) else 0) = (n: ℝ) * ((n: ℝ) - 1) / 2 := by
    -- replace sum over `Fin n × Fin n` with two nested sums over `Fin n`
    rw [Fintype.sum_prod_type]
    -- change order of sum signs (and, correspondingly, the summand under them) and simplify
    rw [Finset.sum_comm]
    simp
    -- replace sum over all `Fin n` to sum over `Finset.range n`
    rw [Finset.sum_fin_eq_sum_range]
    -- tiny result about cardinality of certain set
    have H: ∀ i (h: i < n), (Finset.filter (fun (k: Fin n) => k < ⟨i, h⟩) Finset.univ).card = i := by
      intros i h
      rw [Finset.filter_gt_eq_Iio]
      simp only [Fin.card_Iio]
    -- use this result `H` to rewrite in the goal to make it simpler
    simp_rw [H]
    -- simplify a bit to transform `dite` to `ite` (or simple expression with unnamed conditional)
    simp only [dite_eq_ite]
    -- now a few rewrites solve the goal.
    -- first we use the fact that for all values from `Finset.range n`
    -- the condition in the goal is always true (to simplify the goal)
    rw [Finset.sum_ite_of_true (by simp)]
    -- now move the coercion from `ℕ` to `ℝ` from the inside of the sum to the outside
    rw [<- Nat.cast_sum (β := ℝ)]
    -- useful lemma, that gives formula for the sum of the first `n` natural numbers
    -- (from `0` to `n - 1`, inclusice)
    rw [Finset.sum_range_id n]
    -- the remaining goal is exactly the lemma `aux_5`
    rw [aux_5]

  -- finally an important step of the proof will be done done (in the following lemma)
  have important_result: ∑ i, f i ≤ (n: ℝ) * (n - 1) / 2 := by
    -- unfold the definition of `f`
    simp [f]
    -- quite a few rewrites using lemmas we proved previously
    -- and also some library lemmas
    rw [<- Fintype.sum_prod_type', aux_1]
    rw [aux_2, zero_add]
    rw [aux_3, <- Finset.sum_add_distrib]
    simp_rw [ite_add_ite, add_zero]
    -- make a hypothesis `h` that is about (nonstrict) inequality of two sums
    -- after a rewrite in it using a lemma we proved previously it becomes equal to the goal
    have H := Finset.sum_le_sum (N := ℝ) aux_4
    rw [aux_6] at H
    exact H

  -- let's prove existence of some good index `i: Fin n`
  -- the idea is then to use value `x i` for the proof
  have existence_of_some_good_index: ∃ (i: Fin n), f i ≤ ((n: ℝ) - 1) / 2 := by
    -- let's assume the negation of the goal and reach some contradiction (`False`)
    by_contra Hneg
    -- simplify `Hneg` to change negation of existence to universal quantifier
    simp at Hneg
    -- let's prove that `↑n * (↑n - 1) / 2`  is sum over `Fin n`
    -- where each value under sum sign is the same constant `(↑n - 1) / 2`
    have H: (n: ℝ) * (↑n - 1) / 2 = ∑ (i: Fin n), (((n: ℝ) - 1) / 2) := by
      rw [Fin.sum_const]
      simp
      field_simp
    -- rwwrite using the `H` in the hypothesis `important_result`
    rw [H] at important_result
    -- one step until the contradiction
    -- we prove the opposite of `important_result`
    have H0: (∑ (i: Fin n), ((n: ℝ) - 1) / 2) < ∑ i, f i :=
      Finset.sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, by simp⟩ (by simp; exact Hneg)
    -- and now `linarith` finds the contradiction
    linarith

  -- remaining is easy - get the index `i` and use `x i` to close the goal
  obtain ⟨i, Hi⟩ := existence_of_some_good_index
  use (x i)