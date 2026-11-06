import Mathlib

theorem number_theory_7817 :
    {(m, n) : ℤ × ℤ | m ^ 4 + (m + 1) ^ 4 = n ^ 2 + (n + 1) ^ 2} =
    {(-1, 0), (0, 0), (-1, -1), (0, -1)} := by
  ext ⟨m, n⟩
  simp
  constructor
  · -- Assume (m, n) satisfies the equation
    rintro H
    have h1 : m ^ 4 + (m + 1) ^ 4 = n ^ 2 + (n + 1) ^ 2 := H
    have eq1 : m * (m + 1) * (m ^ 2 + m + 2) = n * (n + 1) := by
      nlinarith [sq_nonneg (m ^ 2 - n), sq_nonneg (m + 1), sq_nonneg (n + 1)]
    have eq2 : 4 * (m * (m + 1) * (m ^ 2 + m + 2)) = (2 * n + 1) ^ 2 - 1 := by
      nlinarith [eq1, sq_nonneg (n + 1)]
    have eq3 : (2 * (m ^ 2 + m + 1)) ^ 2 - (2 * n + 1) ^ 2 = 3 := by
      nlinarith [eq2, sq_nonneg (m ^ 2 + m), sq_nonneg (2 * m), sq_nonneg (2 * m + 1)]
    have eq4 : (2 * (m ^ 2 + m + 1) - (2 * n + 1)) * (2 * (m ^ 2 + m + 1) + (2 * n + 1)) = 3 := by
      nlinarith [eq3]
    have h2 : (2 * (m ^ 2 + m + 1) - (2 * n + 1)) * (2 * (m ^ 2 + m + 1) + (2 * n + 1)) = 3 := eq4
    have h3 : (2 * (m ^ 2 + m + 1) - (2 * n + 1)) ∣ 3 := by
      use (2 * (m ^ 2 + m + 1) + (2 * n + 1))
      all_goals nlinarith
    have h4 : (2 * (m ^ 2 + m + 1) - (2 * n + 1)) ≤ 3 := by
      apply Int.le_of_dvd (by norm_num) h3
    have h5 : (2 * (m ^ 2 + m + 1) - (2 * n + 1)) ≥ -3 := by
      have h6 : - (2 * (m ^ 2 + m + 1) - (2 * n + 1)) ∣ 3 := by
        exact Int.neg_dvd.2 h3
      have h7 : - (2 * (m ^ 2 + m + 1) - (2 * n + 1)) ≤ 3 := by
        apply Int.le_of_dvd (by norm_num) h6
      omega
    interval_cases h6 : (2 * (m ^ 2 + m + 1) - (2 * n + 1)) <;> 
      try { 
        have : m ≤ 1 := by nlinarith
        have : m ≥ -2 := by nlinarith
        have : n ≤ 1 := by nlinarith
        have : n ≥ -2 := by nlinarith
        interval_cases m <;> interval_cases n <;> tauto 
      }
  · -- Show these four solutions satisfy the equation
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- (-1, 0)
      norm_num
    · -- (0, 0)
      norm_num
    · -- (-1, -1)
      norm_num
    · -- (0, -1)
      norm_num