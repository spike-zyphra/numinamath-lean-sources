import Mathlib
import Init.Data.Nat.Gcd

/- 2. A sequence of positive integers $a_{1}, a_{2}, \ldots, a_{n}$ is called a ladder of length $n$ if it consists of $n$ consecutive numbers, in increasing order.

(a) Prove that for every positive integer $n$ there exist two ladders of length $n$, with no elements in common, $a_{1}, a_{2}, \ldots, a_{n}$ and $b_{1}, b_{2}, \ldots, b_{n}$, such that for every $i$ between 1 and $n$ the greatest common divisor of $a_{i}$ and $b_{i}$ is equal to 1.

(b) Prove that for every positive integer $n$ there exist two ladders of length $n$, with no elements in common, $a_{1}, a_{2}, \ldots, a_{n}$ and $b_{1}, b_{2}, \ldots, b_{n}$, such that for every $i$ between 1 and $n$ the greatest common divisor of $a_{i}$ and $b_{i}$ is greater than 1. -/
theorem number_theory_137410_1 (n : ℕ) (hn : 0 < n) :
    (∃ a b : ℕ, a > 0 ∧ b > 0 ∧
    (∀ i ∈ Finset.range n, Nat.gcd (a + i) (b + i) = 1) ∧
    (∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, a + i ≠ b + j)) := by
  -- use 1, .., n for first sequence
  use 1
  -- consider prime larger than n
  let p := Classical.choose (Nat.exists_infinite_primes (n + 1))
  have ⟨hnp, hp⟩ : n + 1 ≤ p ∧ Nat.Prime p :=
    Classical.choose_spec (Nat.exists_infinite_primes (n + 1))
  -- second sequence is 1 + p, ... , n + p
  use 1 + p
  simp
  and_intros
  -- for any i, d ∣ i  and d ∣ i + p means d ∣ p
  . rintro i hi
    simp [Nat.gcd_eq_iff]
    rintro d hd1 hd2
    have hd3 := Nat.dvd_sub (by omega) hd2 hd1
    conv_rhs at hd3 => equals p => omega
    -- but d ∣ i means d ≤ i < p, so d = 1, hence i, i + p are coprime
    have hdp : d ≤ 1 + i := Nat.le_of_dvd (by omega) hd1
    replace hdp : d < p := by omega
    obtain rfl | rfl := Nat.Prime.eq_one_or_self_of_dvd hp _ hd3
    . rfl
    . simp at hdp
  -- since largest value of first sequence is smaller than smallest value of second seqeuence all values are distinct
  . rintro i hi j hj
    omega

theorem number_theory_137410_2 (n : ℕ) (hn : 0 < n) :
    (∃ a b : ℕ, a > 0 ∧ b > 0 ∧
    (∀ i ∈ Finset.range n, Nat.gcd (a + i) (b + i) > 1) ∧
    (∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, a + i ≠ b + j)) := by
  -- use 2, ..., n + 1 for first sequnce
  use 2
  -- consider m = (n+1)!
  let m := (n + 1).factorial 
  have h_n_lt_m : n + 1 ≤ m := Nat.self_le_factorial _
  -- use 2 + m, .... (n+1) + m for second sequence
  use 2 + m
  simp
  and_intros
  -- now gcd of i and i + m is i becuase i ∣ i + m as i ≤ (n + 1), hence not coprime
  . rintro i hi
    have hd : 2 + i ∣ 2 + m + i := by
      rw [add_assoc, add_comm m, ← add_assoc]
      rw [Nat.dvd_add_self_left]
      apply Nat.dvd_factorial
      . omega
      . omega
    rw [Nat.gcd_eq_left hd]
    linarith
  -- again since largest value of first sequence is smaller than smallest value of second seqeuence all values are distinct
  . rintro i hi j hj
    omega