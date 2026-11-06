import Mathlib

/- A three-digit natural number, when divided by $2$, $3$, $4$, $5$, and $7$, leaves a remainder of $1$ in each case. The smallest three-digit number with this property is ___          ___ ; the largest three-digit number is ___          ___. -/
theorem number_theory_2811 :
    IsLeast {n | n ∈ Finset.Icc 100 999 ∧ n % 2 = 1 ∧ n % 3 = 1 ∧ n % 4 = 1 ∧ n % 5 = 1 ∧ n % 7 = 1} 421 ∧
    IsGreatest {n | n ∈ Finset.Icc 100 999 ∧ n % 2 = 1 ∧ n % 3 = 1 ∧ n % 4 = 1 ∧ n % 5 = 1 ∧ n % 7 = 1} 841 := by
  constructor
  · constructor
    · -- Show that 421 is in the set
      constructor
      · simp [Finset.mem_Icc]
      norm_num
    · -- Show that there's no smaller element in the set
      intro n hn
      rcases hn with ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩
      simp only [Finset.mem_Icc] at hn1
      have h1 : 100 ≤ n := hn1.1
      have h2 : n ≤ 999 := hn1.2
      by_contra h
      push_neg at h
      interval_cases n <;> omega
  · constructor
    · -- Show that 841 is in the set
      constructor
      · simp [Finset.mem_Icc]
      norm_num
    · -- Show that there's no larger element in the set
      intro n hn
      rcases hn with ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩
      simp only [Finset.mem_Icc] at hn1
      have h1 : 100 ≤ n := hn1.1
      have h2 : n ≤ 999 := hn1.2
      by_contra h
      push_neg at h
      have h3 : n > 841 := by linarith
      -- we need to show n <= 841
      have h4 : n > 841 := by linarith
      have h5 : n ≤ 999 := by linarith
      interval_cases n <;> omega