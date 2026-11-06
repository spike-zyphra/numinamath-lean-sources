import Mathlib

/- The squares of two positive integers differ by 2016. Find the maximum possible sum of the two integers.

[i]Proposed by Clive Chan -/
theorem number_theory_30963:
IsGreatest {n | ∃ a b: ℕ, a > 0 ∧ b > 0 ∧ n = a + b ∧ |(a ^ 2 : ℤ) - (b ^ 2)| = 2016} 1008 := by
  
  unfold IsGreatest upperBounds
  simp
  constructor

  --505 and 503 give 1008.
  use 505
  simp
  use 503
  simp

  --Now, for every pair a b  WLOG assume a > b.
  intro n a apos b bpos hn h

  have aneb : a ≠ b := by 
    by_contra aeb
    simp [aeb] at h
  wlog agb : a > b
  have bga : b > a := by omega
  apply this
  exact bpos
  exact apos
  omega
  have : |(b:ℤ)^2-a^2| = |(a:ℤ)^2-b^2| := by exact abs_sub_comm ((b:ℤ) ^ 2) (↑a ^ 2)
  rw [this]
  exact h
  omega
  exact bga

  --Then, we have that (a+b)*(a-b) = 2016, by rewriting our assumption.
  have eq : (a+b) * (a-b) = 2016 := by 
    have t1: ((a:ℤ)+b) * (a-b) = 2016 := by
      have : 0 < (a : ℤ)^2 - b^2 := by 
        refine Int.sub_pos_of_lt ?_
        exact Int.natAbs_lt_iff_sq_lt.mp agb
      have : @abs ℤ instLatticeInt Int.instAddGroup (↑a ^ 2 - ↑b ^ 2) = a^2 - b^2 := by exact abs_of_pos this
      rw [this] at h
      have : (a:ℤ)^2 -b^2 = (a+b)*(a-b) := by ring
      rw [this] at h
      exact h
    zify
    have : @Nat.cast ℤ AddMonoidWithOne.toNatCast (a - b) = a-b := by omega
    rw [this]
    exact t1
  have : (a-b) ≠ 0 := by exact Nat.sub_ne_zero_iff_lt.mpr agb

  --It cannot happen that a - b = 1.
  by_cases ambe1 : a-b = 1
  simp [ambe1] at eq
  have : 2 * b = 2015 := by omega
  omega

  --Hence a-b≥2, and a+b ≤ 2016/2 = 1008.
  have ambge2 : 2 ≤ a - b := by omega
  rw [hn]
  nlinarith