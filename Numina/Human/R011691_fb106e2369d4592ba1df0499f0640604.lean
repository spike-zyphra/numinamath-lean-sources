import Mathlib

/- $4 \cdot 252$ (1) Find all positive integers, the first digit of which is 6, and removing this 6, the resulting integer is $\frac{1}{25}$ of the original integer.
(2) Prove: There is no such positive integer, the first digit of which is 6, and removing this 6, the resulting integer is $\frac{1}{35}$ of the original integer. -/
theorem number_theory_274432 :
    let first_digit: ℕ → ℕ := fun n => (Nat.digits 10 n).getLastI
    let remaining_part: ℕ → ℕ := fun n => Nat.ofDigits 10 ((Nat.digits 10 n).dropLast)
    (∀ (n: ℕ) (Hn: 0 < n), (first_digit n = 6 ∧ remaining_part n = (1 / 25 : ℚ) * n) ↔ (∃ p, n = 625 * 10 ^ p)) ∧
    ¬ (∃ (n: ℕ), 0 < n ∧ first_digit n = 6 ∧ remaining_part n = (1 / 35 : ℚ) * n) := by

  intros first_digit remaining_part

  -- let's start with six auxiliary lemmas

  -- the first is about such property of nonempty list:
  -- if we drop the last element of it and then
  -- append last element back to the end,
  -- we get the original list
  have aux_1 (L: List ℕ) (HL: L ≠ List.nil): L.dropLast ++ [L.getLastI] = L := by
    nth_rw 3 [<- List.dropLast_append_getLast HL]
    congr
    rw [List.getLastI_eq_getLast?]
    rw [List.getLast?_eq_getLast_of_ne_nil]

  -- the second is about the fact that
  -- nonzero natural number has nonempty list of digits
  have aux_2 (n: ℕ) (Hn: 0 < n): Nat.digits 10 n ≠ [] := by
    have H1: n ≠ 0 := by omega
    exact Nat.digits_ne_nil_iff_ne_zero.mpr H1

  -- the third auxiliary lemma:
  -- it is application of the first to list of digits of nonzero natural number
  have aux_3 (n: ℕ) (Hn: 0 < n):
      Nat.digits 10 n = (Nat.digits 10 n).dropLast ++ [(Nat.digits 10 n).getLastI] := by
    rw [aux_1 (Nat.digits 10 n) (aux_2 n Hn)]

  -- the fourth auxiliary lemma:
  -- any nonzero natural number can be expressed as the sum of
  -- it's leading digit multiplied by the correct power of 10 and
  -- the remaining part what's left after removing the first digit
  have aux_4 (n: ℕ) (Hn: 0 < n):
      n = Nat.ofDigits 10 (Nat.digits 10 n).dropLast +
         10 ^ ((Nat.digits 10 n).length - 1) * (Nat.digits 10 n).getLastI := by
    have H: Nat.ofDigits 10 (Nat.digits 10 n) =
             Nat.ofDigits 10 ((Nat.digits 10 n).dropLast ++ [(Nat.digits 10 n).getLastI]) := by
      nth_rw 1 [aux_3 n Hn]
    rw [Nat.ofDigits_digits] at H
    rw [Nat.ofDigits_append] at H
    simp at H
    exact H

  -- the fifth auxiliary lemma:
  -- for any nonzero natural number
  -- the remaining part (after removing the first digit)
  -- is less than `10` to power that's one less than number of digits of the number
  have aux_5 (n: ℕ) (Hn: 0 < n):
      Nat.ofDigits 10 (Nat.digits 10 n).dropLast < 10 ^ ((Nat.digits 10 n).length - 1) := by
    have H: ∀ x ∈ (Nat.digits 10 n).dropLast, x < 10 := by
      intros x Hx
      apply List.mem_of_mem_dropLast at Hx
      exact Nat.digits_lt_base' Hx
    have H0 := Nat.ofDigits_lt_base_pow_length (by norm_num) H
    simp at H0
    exact H0

  -- the sixth auxiliary lemma:
  -- last element of nonempty list belongs to this list
  have aux_6 (L: List ℕ) (HL: L ≠ []): L.getLastI ∈ L := by
    rw [List.getLastI_eq_getLast?]
    rw [List.getLast?_eq_getLast_of_ne_nil HL]
    simp


  -- additional definition: function that returns
  -- number of digits of natural number.
  -- used as an abbreviature, basically
  set number_of_digits: ℕ → ℕ := fun n => (Nat.digits 10 n).length

  -- this lemma is the same as lemma `aux_5`, except
  -- it's formulated using functions
  -- `remaining_part`, `number_of_digits`
  have remaining_parts_lt_10_pow (n: ℕ) (Hn: 0 < n):
      remaining_part n < 10 ^ (number_of_digits n - 1) := by
    unfold remaining_part number_of_digits
    exact aux_5 n Hn

  -- finally we get to the important lemma about any nonzero number:
  -- it is equal to the sum of the first digit multiplied
  -- by the appropriate power of `10` and
  -- remaining part that's left after removing the first number
  have parts_of_number (n: ℕ) (Hn: 0 < n):
      n = first_digit n * 10 ^ (number_of_digits n - 1) + remaining_part n := by
    unfold first_digit number_of_digits remaining_part
    nth_rw 1 [aux_4 n Hn]
    ring


  -- let's start proving the goal
  constructor

  . -- the first part is about characterization of such natural numbers,
    -- that becomes 25 times smaller after removing the first digit which is `6`
    intros n Hn
    constructor <;> intro H
    . -- first part
      -- at the start we destruct hypothesis `H`
      obtain ⟨H0, H1⟩ := H
      -- then simplify the hypothesis `H1` (which we got from destructing `H`)
      -- to remove that division by `25`
      -- and after that we move from rational numbers to natural numbers
      -- using tactic `norm_cast`
      field_simp at H1
      norm_cast at H1
      -- we replace the number `n` with it's parts in the right side of the equality
      -- of the hypothesis `H1`, then we rewrite `first_digit` to `6`
      nth_rw 2 [parts_of_number n Hn] at H1
      rw [H0] at H1
      -- make new, more simple version of hypothesis `H1`
      have H2: remaining_part n * 4 = 10 ^ (number_of_digits n - 1) := by omega
      -- number of digits can be `0`, `1`, `2` or at least `3`.
      -- first three cases are impossible and causes a contradiction and
      -- the only meaningful case is the last one
      have H3: number_of_digits n = 0 ∨ number_of_digits n = 1 ∨
               number_of_digits n = 2 ∨ 3 ≤ number_of_digits n := by omega
      obtain H3 | H3 | H3 | H3 := H3
      . rw [H3] at H2
        simp at H2
      . rw [H3] at H2
        simp at H2
      . rw [H3] at H2
        simp at H2
        omega
      . -- if number of digits is at least `3`, we have to do some actual work.
        -- we substract `3` from the number of digits, and
        -- use this difference as a witness for the goal about existence
        use (number_of_digits n - 3)
        -- number `n` is replaced by the sum of two of its parts
        -- (only in the first occurence in the goal)
        nth_rw 1 [parts_of_number n Hn]
        -- some useful rewrites
        rw [show number_of_digits n - 1 = number_of_digits n - 3 + 2 by omega] at H1 ⊢
        rw [Nat.pow_add] at H1 ⊢
        -- now we can express remaining part of the number
        -- (after removing the first digit)
        -- as the expression of its number of digits
        have H4: remaining_part n = 25 * 10 ^ (number_of_digits n - 3) := by omega
        -- the goal becomes simple enough for the tactic `omega`
        -- after the last two rewrites
        rw [H0, H4]
        omega
    . -- second part is about proving that any number of form `625 * 10 ^ p`
      -- has the property that removing the first digit makes it `25` times smaller
      obtain ⟨p, Hp⟩ := H
      subst n
      refine ⟨?_, ?_⟩
      . -- we have to prove that the first digit of such number is equal to `6`
        -- this obvious fact takes unfolding `first_digit` and
        -- some rewrites and simplifications
        unfold first_digit
        rw [mul_comm]
        -- the first three digits of the number `10 ^ p * 625` are, of course, `625`,
        -- and the remaining digits are zeroes, repeated `p` times.
        -- this is what we prove using the library lemma
        rw [Nat.digits_base_pow_mul (by norm_num) (by norm_num)]
        simp
        -- we move from `getLastI` to `getLast?` and then further to `getLast`
        -- because simplification work only on the last one
        rw [List.getLastI_eq_getLast?]
        rw [List.getLast?_eq_getLast_of_ne_nil (by simp)]
        simp
      . -- we have to prove that the remaining part actually becomes `25` times smaller.
        -- we simplify the goal to remove the division by `25` and
        -- then move from rational numbers to natural numbers, using tactic `norm_cast`
        field_simp
        norm_cast
        -- unfold the defition of `remaining_part`
        unfold remaining_part
        -- simple rewrite to make the goal good for the library lemma
        nth_rw 1 [mul_comm 625]
        -- same as previously, we use the fact that
        -- the first digits of the number is `625` and
        -- the remaining numbers are `p` zeroes
        rw [Nat.digits_base_pow_mul (by norm_num) (by norm_num)]
        simp
        -- we show that `[5, 2]` are digits of numbers of `25` (for lemma to work)
        rw [show [5, 2] = Nat.digits 10 25 by simp]
        -- we transform the goal back to the form `25 * 10 ^ p`
        rw [<- Nat.digits_base_pow_mul (by norm_num) (by norm_num)]
        -- the functions `Nat.ofDigits` and `Nat.digits` cancels out
        rw [Nat.ofDigits_digits]
        -- and now the goal is simple enough for the tactic `ring` to work
        ring

  . -- the second part of the goal is about impossibility of a number,
    -- that starts with `6` and becomes `35` times smaller
    -- after removing its first digit.
    -- we suppose that such number exists and try to reach a contradiction
    intro H
    obtain ⟨n, Hn, H0, H1⟩ := H
    -- the same method as previously:
    -- tactic `field_simp` to get rid of the division in the hypothesis `H1` and
    -- then tactic `norm_cast` to change it to equality in natural numbers
    field_simp at H1
    norm_cast at H1
    -- express the number `n` as the combination of two parts
    -- (the first digit or `6` multiplied by the appropriate power of `10` and
    -- remaining part) - but only in the right side of the equality `H1`,
    -- and don't forget to rewrite `first_digit n` to `6`
    nth_rw 2 [parts_of_number n Hn] at H1
    rw [H0] at H1
    -- now we get to the act that some expression is divided by `17`
    have H2: remaining_part n * 17 = 3 * 10 ^ (number_of_digits n - 1) := by omega
    have H3: 17 ∣ 3 * 10 ^ (number_of_digits n - 1) := by omega
    -- as we know, natural number `17` is a prime
    have Hprime: Nat.Prime 17 := by norm_num
    -- there's no way for prime number `17` to divide
    -- the expression `3 * 10 ^ (number_of_digits n - 1)`,
    -- because it doesn't divide `3` and doesn't divide `10` too
    rw [Nat.Prime.dvd_mul Hprime] at H3
    obtain H3 | H3 := H3
    . omega
    . apply Nat.Prime.dvd_of_dvd_pow Hprime at H3
      omega