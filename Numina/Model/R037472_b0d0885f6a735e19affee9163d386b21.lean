import Mathlib

def S : ℕ → ℕ
| n => (Nat.digits 10 n).sum

theorem number_theory_5798 :
    IsGreatest {n | n < 2019 ∧ S n = S (2 * n)} 2016 := by
  constructor
  · -- First, we verify that 2016 is in the set.
    constructor
    · norm_num
    · native_decide
  · -- Now, we need to prove that for any n in the set, n ≤ 2016.
    intro n hn
    rcases hn with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : n = 2017 ∨ n = 2018 := by 
      omega 
    rcases h3 with (r | r)
    · -- n = 2017
      rw [r] at h2 
      norm_num [S] at h2 
    · -- n = 2018
      rw [r] at h2 
      norm_num [S] at h2