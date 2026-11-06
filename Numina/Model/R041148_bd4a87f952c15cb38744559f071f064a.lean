import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_317571 (a b : ℝ) :
  ∃ x y : ℝ, x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ |x * y - a * x - b * y| ≥ 1 / 3 := by
  by_cases h1 : |(0 : ℝ) * (0 : ℝ) - a * (0 : ℝ) - b * (0 : ℝ)| ≥ 1 / 3
  · -- Case where (0,0) satisfies the inequality
    use 0, 0
    constructor
    · -- Show 0 ∈ [0,1]
      norm_num [mem_Icc]
    constructor
    · -- Show 0 ∈ [0,1]
      norm_num [mem_Icc]
    · -- Show |0 * 0 - a * 0 - b * 0| ≥ 1 / 3
      simpa using h1
  · -- Case where (0,0) does not satisfy the inequality
    by_cases h2 : |(0 : ℝ) * (1 : ℝ) - a * (0 : ℝ) - b * (1 : ℝ)| ≥ 1 / 3
    · -- Case where (0,1) satisfies the inequality
      use 0, 1
      constructor
      · -- Show 0 ∈ [0,1]
        norm_num [mem_Icc]
      constructor
      · -- Show 1 ∈ [0,1]
        norm_num [mem_Icc]
      · -- Show |0 * 1 - a * 0 - b * 1| ≥ 1 / 3
        simpa using h2
    · -- Case where (0,1) does not satisfy the inequality
      by_cases h3 : |(1 : ℝ) * (0 : ℝ) - a * (1 : ℝ) - b * (0 : ℝ)| ≥ 1 / 3
      · -- Case where (1,0) satisfies the inequality
        use 1, 0
        constructor
        · -- Show 1 ∈ [0,1]
          norm_num [mem_Icc]
        constructor
        · -- Show 0 ∈ [0,1]
          norm_num [mem_Icc]
        · -- Show |1 * 0 - a * 1 - b * 0| ≥ 1 / 3
          simpa using h3
      · -- Case where (1,0) does not satisfy the inequality
        use 1, 1
        constructor
        · -- Show 1 ∈ [0,1]
          norm_num [mem_Icc]
        constructor
        · -- Show 1 ∈ [0,1]
          norm_num [mem_Icc]
        · -- Show |1 * 1 - a * 1 - b * 1| ≥ 1 / 3
          by_contra h
          push_neg at h
          have h1' : |(0 : ℝ) * (0 : ℝ) - a * (0 : ℝ) - b * (0 : ℝ)| < 1 / 3 := by
            simpa using h1
          have h2' : |(0 : ℝ) * (1 : ℝ) - a * (0 : ℝ) - b * (1 : ℝ)| < 1 / 3 := by
            simpa using h2
          have h3' : |(1 : ℝ) * (0 : ℝ) - a * (1 : ℝ) - b * (0 : ℝ)| < 1 / 3 := by
            simpa using h3
          have h4 : |(1 * 1 - a * 1 - b * 1)| < 1 / 3 := by
            simpa using h
          cases' abs_lt.mp h2' with h2_neg h2_pos
          cases' abs_lt.mp h3' with h3_neg h3_pos
          cases' abs_lt.mp h4 with h4_neg h4_pos
          all_goals
            norm_num [mem_Icc] at *
            all_goals
              linarith