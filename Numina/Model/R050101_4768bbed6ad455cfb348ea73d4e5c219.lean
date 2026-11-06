import Mathlib

theorem algebra_128313 {n m : ℕ} (hn : n > 0) (hm : m > 0)
    (h1 : m = 10 * n) (h2 : m * 45 = n * 10) :
    n = 1 ∧ m = 10 := by
  rw [h1] at h2
  have h3 : 10 * n * 45 = n * 10 := by 
    linarith
  have h4 : 440 * n = 0 := by 
    omega 
  have h5 : n = 0 := by 
    omega 
  linarith