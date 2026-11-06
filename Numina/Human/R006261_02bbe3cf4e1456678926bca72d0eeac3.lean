import Mathlib

/-Let $K$ be a positive integer. Find all odd natural numbers $n$ such that
$500 < n < 1000$ and the sum of the last digits of all divisors of $n$ (including 1 and $n$ itself) is $K$.
Show that if $K=21$, the only such number $n$ is $625$.-/

theorem number_theory_635258: {n: ℕ | 500 < n ∧ n < 1000 ∧ Odd n ∧ ∑ i ∈ Nat.divisors n, i % 10 = 21} = {625} := by

  ext n
  constructor

  -- the forward direction
  .
    intro h
    simp at h
    simp
    by_contra! ne
    rcases h with ⟨l1, l2, o, h⟩
    apply Odd.exists_bit1 at o
    obtain ⟨m, o⟩ := o
    simp [o] at *
    replace ne: m ≠ 312 := by omega
    replace l1: 249 ≤ m := by
      clear *- l1
      omega
    replace l2: m ≤ 499 := by
      clear *- l2
      omega
    by_cases l: m ≤ 311

    -- m ≤ 311
    .
      clear l2 ne
      absurd h
      interval_cases m
      all_goals native_decide

    -- 313 ≤ m
    .
      replace l: 313 ≤ m := by
        omega
      clear l1 ne
      absurd h
      interval_cases m
      all_goals native_decide

  -- the backward direction
  .
    intro h
    simp at h
    simp [h]
    native_decide