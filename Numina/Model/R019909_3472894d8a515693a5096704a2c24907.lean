import Mathlib

open scoped BigOperators

theorem algebra_281242 {a : ℕ → ℝ}
  (ha1 : a 1 = 1)
  (han : ∀ n ≥ 2, a n = a (n - 1) + 1 / (n * (n - 1))) :
  a 4 = 7 / 4 := by
  have h1 : a 2 = a (2 - 1) + 1 / (2 * (2 - 1)) := by
    specialize han 2 (by norm_num)
    simpa using han
  rw [show (2 - 1 : ℕ) = 1 by norm_num] at h1 
  rw [ha1] at h1
  have h2 : a 2 = 3 / 2 := by 
    rw [h1]
    norm_num
  have h3 : a 3 = a (3 - 1) + 1 / (3 * (3 - 1)) := by 
    specialize han 3 (by norm_num)
    simpa using han
  rw [show (3 - 1 : ℕ) = 2 by norm_num] at h3 
  rw [h2] at h3
  have h4 : a 3 = 5 / 3 := by 
    rw [h3]
    norm_num
  have h5 : a 4 = a (4 - 1) + 1 / (4 * (4 - 1)) := by 
    specialize han 4 (by norm_num)
    simpa using han
  rw [show (4 - 1 : ℕ) = 3 by norm_num] at h5 
  rw [h4] at h5
  rw [h5]
  norm_num