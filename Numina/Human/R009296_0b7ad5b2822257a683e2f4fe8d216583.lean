import Mathlib

/-What is the product of the two largest one-digit primes and the largest two-digit prime?-/
theorem algebra_16588 : (Nat.Prime 5)∧(¬Nat.Prime 6)∧(Nat.Prime 7)∧(Nat.Prime 97)∧(¬∃n<10, n > 7 ∧ Nat.Prime n)∧(¬∃n<100, n > 97 ∧ Nat.Prime n)∧(5 * 7 * 97 = 3395) := by
  -- it means that 5, 7 are the two largest one-digit primes, and  the largest two-digit prime is 97.
  -- the productor of them is 3395.

  constructor
  . -- 5 is prime
    norm_num
  constructor
  . -- 6 is not prime
    norm_num
  constructor
  . -- 7 is prime
    norm_num
  constructor
  . -- 97 is prime
    norm_num
  constructor
  . -- there is no prime number between 7 and 10
    have n8 : ¬Nat.Prime 8 := by
      norm_num
    have n9 : ¬Nat.Prime 9 := by
      norm_num
    simp
    intro x hr hl
    by_cases h: x = 8
    . rw [h]
      exact n8
    by_cases h': x = 9
    . rw [h']
      exact n9
    simp at h
    simp at h'
    have : 8 ≤ x := by linarith
    have : x ≤ 9 := by linarith
    have hl : 8 < x := by
      rcases (Ne.lt_or_lt h) with h₁ | h₂
      . absurd h₁
        linarith
      . exact h₂
    have : 9 <= x := by linarith
    have hr : x = 9 := by linarith
    absurd hr
    exact h'
  constructor
  . -- there is no prime number between 97 and 100
    simp
    have n98 : ¬Nat.Prime 98 := by
      norm_num
    have n99 : ¬Nat.Prime 99 := by
      norm_num
    intro x hr hl
    by_cases h: x = 98
    . rw [h]
      exact n98
    by_cases h': x = 99
    . rw [h']
      exact n99
    simp at h
    simp at h'
    have : 98 ≤ x := by linarith
    have : x ≤ 99 := by linarith
    have hl : 98 < x := by
      rcases (Ne.lt_or_lt h) with h₁ | h₂
      . absurd h₁
        linarith
      . exact h₂
    have : 99 <= x := by linarith
    have hr : x = 99 := by linarith
    absurd hr
    exact h'
  linarith
