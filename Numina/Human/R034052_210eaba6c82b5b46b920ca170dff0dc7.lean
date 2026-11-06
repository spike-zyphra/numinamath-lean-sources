import Mathlib
/-
In Yang's number theory class, Michael K, Michael M, and Michael R take a series of tests. Afterwards, Yang makes the following observations about the test scores:
(a) Michael K had an average test score of 90, Michael M had an average test score of 
91, and Michael R had an average test score of 92.
(b) Michael K took more tests than Michael M, who in turn took more tests than Michael R.
(c) Michael M got a higher total test score than Michael R, who in turn got a higher total test score than Michael K. (The total test score is the sum of the test scores over all tests)
What is the least number of tests that Michael K, Michael M, and Michael R could have taken combined?-/
theorem number_theory_48566 :
    IsLeast {n | ∃ k m r : ℕ, n = k + m + r ∧ k > m ∧ m > r ∧ m * 91 > r * 92 ∧ r * 92 > k * 90} 413 := by
  constructor
  · -- First, we'll show 413 is in the set
    use 139, 138, 136
    all_goals norm_num
  · -- Now, prove that 413 is the least element
    intro n hn
    rcases hn with ⟨k, m, r, hsum, h1, h2, h3, h4⟩
    by_contra h
    push_neg at h
    have h5 : k + m + r < 413 := by linarith
    have h6 : k ≥ 139 := by
      by_contra h7
      push_neg at h7
      interval_cases k <;> 
      omega
    have h7 : m ≥ 138 := by
      by_contra h8
      push_neg at h8
      interval_cases m <;> 
      omega
    have h8 : r ≥ 136 := by
      by_contra h9
      push_neg at h9
      interval_cases r <;> 
      omega
    omega