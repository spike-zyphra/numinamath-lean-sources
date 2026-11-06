import Mathlib

theorem algebra_194882 {n m : ℕ} (hnm : n > 0 ∧ m > 0)
    (h : n * m = n + m + 18) : n * m = 40 := by 
  have h1 : n > 0 := hnm.1
  have h2 : m > 0 := hnm.2
  have h3 : n ≤ 20 := by
    by_contra h4
    push_neg at h4
    have h4' : m ≤ 20 := by
      nlinarith [h, h4, mul_pos (show 0 < n by linarith) (show 0 < m by linarith)]
    interval_cases m <;> omega
  have h4 : m ≤ 20 := by
    by_contra h5
    push_neg at h5
    have h5' : n ≤ 20 := by
      nlinarith [h, h5, mul_pos (show 0 < n by linarith) (show 0 < m by linarith)]
    interval_cases n <;> omega
  interval_cases n <;> interval_cases m <;> omega