import Mathlib

open Real

theorem algebra_182550 {t : ℕ → ℝ}
    (ht1 : t 1 = (100 ^ 100 + 1) / (100 ^ 90 + 1))
    (ht2 : t 2 = (100 ^ 99 + 1) / (100 ^ 89 + 1))
    (ht3 : t 3 = (100 ^ 101 + 1) / (100 ^ 91 + 1))
    (ht4 : t 4 = (101 ^ 101 + 1) / (101 ^ 91 + 1))
    (ht5 : t 5 = (101 ^ 100 + 1) / (101 ^ 90 + 1))
    (ht6 : t 6 = (99 ^ 99 + 1) / (99 ^ 89 + 1))
    (ht7 : t 7 = (99 ^ 100 + 1) / (99 ^ 90 + 1)) :
    t 6 < t 7 ∧ t 7 < t 2 ∧ t 2 < t 1 ∧ t 1 < t 3 ∧ t 3 < t 5 ∧ t 5 < t 4 := by
  have h1 : t 6 < t 7 := by
    rw [ht6, ht7]
    norm_num
  have h2 : t 7 < t 2 := by
    rw [ht7, ht2]
    norm_num
  have h3 : t 2 < t 1 := by 
    rw [ht2, ht1]
    norm_num
  have h4 : t 1 < t 3 := by 
    rw [ht1, ht3]
    norm_num
  have h5 : t 3 < t 5 := by 
    rw [ht3, ht5]
    norm_num
  have h6 : t 5 < t 4 := by 
    rw [ht5, ht4]
    norm_num
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith