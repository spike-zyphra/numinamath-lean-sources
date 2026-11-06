import Mathlib

theorem number_theory_286768 (a : ℕ → ℕ) (ha : ∀ n, a (n + 2) = a n + a (n + 1)) (ha0 : a 0 = 2) (ha2 : a 2 = 9) :
    a 7 = 107 := by
  have ha1 : a 1 = 7 := by
    have h1 : a 2 = a 0 + a 1 := ha 0
    rw [ha0] at h1
    rw [ha2] at h1
    omega
  have ha3 : a 3 = a 1 + a 2 := ha 1
  rw [ha1, ha2] at ha3
  have ha3_val : a 3 = 16 := by
    omega
  have ha4 : a 4 = a 2 + a 3 := ha 2
  rw [ha2, ha3_val] at ha4
  have ha4_val : a 4 = 25 := by
    omega
  have ha5 : a 5 = a 3 + a 4 := ha 3
  rw [ha3_val, ha4_val] at ha5
  have ha5_val : a 5 = 41 := by
    omega
  have ha6 : a 6 = a 4 + a 5 := ha 4
  rw [ha4_val, ha5_val] at ha6
  have ha6_val : a 6 = 66 := by
    omega
  have ha7 : a 7 = a 5 + a 6 := ha 5
  rw [ha5_val, ha6_val] at ha7
  omega