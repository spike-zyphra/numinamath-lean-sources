import Mathlib
/- Last year, Isabella took 7 math tests and received 7 different scores, each an integer between 91 and 100, inclusive. After each test she noticed that the average of her test scores was an integer. Her score on the seventh test was 95. What was her score on the sixth test?
(A) 92(B) 94(C) 96(D) 98(E) 100 -/
theorem number_theory_97765 
  (s1 s2 s3 s4 s5 s6 s7 : ℕ)
  (h_range1 : 91 ≤ s1 ∧ s1 ≤ 100)
  (h_range2 : 91 ≤ s2 ∧ s2 ≤ 100)
  (h_range3 : 91 ≤ s3 ∧ s3 ≤ 100)
  (h_range4 : 91 ≤ s4 ∧ s4 ≤ 100)
  (h_range5 : 91 ≤ s5 ∧ s5 ≤ 100)
  (h_range6 : 91 ≤ s6 ∧ s6 ≤ 100)
  (h_range7 : 91 ≤ s7 ∧ s7 ≤ 100)
  (h_distinct : s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s1 ≠ s5 ∧ s1 ≠ s6 ∧ s1 ≠ s7 ∧
                 s2 ≠ s3 ∧ s2 ≠ s4 ∧ s2 ≠ s5 ∧ s2 ≠ s6 ∧ s2 ≠ s7 ∧
                 s3 ≠ s4 ∧ s3 ≠ s5 ∧ s3 ≠ s6 ∧ s3 ≠ s7 ∧
                 s4 ≠ s5 ∧ s4 ≠ s6 ∧ s4 ≠ s7 ∧
                 s5 ≠ s6 ∧ s5 ≠ s7 ∧
                 s6 ≠ s7)
  (h_avg1 : ∃ a1 : ℕ, s1 = 1 * a1)
  (h_avg2 : ∃ a2 : ℕ, s1 + s2 = 2 * a2)
  (h_avg3 : ∃ a3 : ℕ, s1 + s2 + s3 = 3 * a3)
  (h_avg4 : ∃ a4 : ℕ, s1 + s2 + s3 + s4 = 4 * a4)
  (h_avg5 : ∃ a5 : ℕ, s1 + s2 + s3 + s4 + s5 = 5 * a5)
  (h_avg6 : ∃ a6 : ℕ, s1 + s2 + s3 + s4 + s5 + s6 = 6 * a6)
  (h_avg7 : ∃ a7 : ℕ, s1 + s2 + s3 + s4 + s5 + s6 + s7 = 7 * a7)
  (h_score7 : s7 = 95)
  : s6 = 100 := by
  -- destructure existentials
  obtain ⟨a1, h_avg1⟩ := h_avg1
  obtain ⟨a2, h_avg2⟩ := h_avg2
  obtain ⟨a3, h_avg3⟩ := h_avg3
  obtain ⟨a4, h_avg4⟩ := h_avg4
  obtain ⟨a5, h_avg5⟩ := h_avg5
  obtain ⟨a6, h_avg6⟩ := h_avg6
  obtain ⟨a7, h_avg7⟩ := h_avg7
  -- Clearly, the sum of the first $6$ numbers must be $570$. 
  have cutter : s1 + s2 + s3 + s4 + s5 + s6 = 570 := by omega
  -- In order for the first $5$ numbers to sum to a multiple of $5$, the sixth number must also be a multiple of $5$, since $30$ is a multiple of $5$. Thus, the only option is the sixth number is $10$, which gives $10+90=  \boxed{\textbf{(E) }100}$
  omega