import Mathlib

theorem number_theory_223159 (a : ℕ → ℕ) (ha : a 0 = 5) (ha' : a 1 = 3) (ha'' : a 2 = 3)
    (h : ∀ n, a (n + 3) = a n + a (n + 1) + a (n + 2)) :
    Nat.Prime (a 0) ∧ Nat.Prime (a 1) ∧ Nat.Prime (a 2) ∧ Nat.Prime (a 3) ∧ Nat.Prime (a 4) ∧
    Nat.Prime (a 5) ∧ Nat.Prime (a 6) ∧ Nat.Prime (a 7) ∧ Nat.Prime (a 8) := by

  have ha3 : a 3 = 11 := by
    rw [h 0, ha, ha', ha'']
    all_goals omega

  have ha4 : a 4 = 17 := by
    rw [h 1, ha', ha'', ha3]
    all_goals omega

  have ha5 : a 5 = 31 := by
    rw [h 2, ha'', ha3, ha4]
    all_goals omega

  have ha6 : a 6 = 59 := by
    rw [h 3, ha3, ha4, ha5]
    all_goals omega

  have ha7 : a 7 = 107 := by
    rw [h 4, ha4, ha5, ha6]
    all_goals omega

  have ha8 : a 8 = 197 := by
    rw [h 5, ha5, ha6, ha7]
    all_goals omega

  constructor
  · -- a 0 = 5 is prime
    rw [ha]
    norm_num
  constructor
  · -- a 1 = 3 is prime
    rw [ha']
    norm_num
  constructor
  · -- a 2 = 3 is prime
    rw [ha'']
    norm_num
  constructor
  · -- a 3 = 11 is prime
    rw [ha3]
    norm_num
  constructor
  · -- a 4 = 17 is prime
    rw [ha4]
    norm_num
  constructor
  · -- a 5 = 31 is prime
    rw [ha5]
    norm_num
  constructor
  · -- a 6 = 59 is prime
    rw [ha6]
    norm_num
  constructor
  · -- a 7 = 107 is prime
    rw [ha7
      ]
    norm_num
  · -- a 8 = 197 is prime
    rw [ha8
      ]
    norm_num