import Mathlib

theorem algebra_17057 :
    IsLeast {n : ℤ | ∃ x : ℤ, n = |x + 2| + |x + 4| + |x + 5|} 3 := by
  constructor
  · -- Show that 3 is in the set
    use -4
    norm_num
  · -- Show that 3 is the smallest
    intro n hn
    rcases hn with ⟨x, hx⟩
    by_cases h1 : x + 5 ≥ 0
    · -- x + 5 ≥ 0, i.e., x ≥ -5
      by_cases h2 : x + 4 ≥ 0
      · -- x + 4 ≥ 0, i.e., x ≥ -4
        by_cases h3 : x + 2 ≥ 0
        · -- x + 2 ≥ 0, i.e., x ≥ -2
          rw [abs_of_nonneg h3, abs_of_nonneg h2, abs_of_nonneg h1] at hx
          omega
        · -- x + 2 < 0, i.e., x < -2
          rw [abs_of_neg (not_le.mp h3), abs_of_nonneg h2, abs_of_nonneg h1] at hx
          omega
      · -- x + 4 < 0, i.e., x < -4
        by_cases h3 : x + 2 ≥ 0
        · -- x + 2 ≥ 0, i.e., x ≥ -2
          rw [abs_of_nonneg h3, abs_of_neg (not_le.mp h2), abs_of_nonneg h1] at hx
          omega
        · -- x + 2 < 0, i.e., x < -2
          rw [abs_of_neg (not_le.mp h3), abs_of_neg (not_le.mp h2), abs_of_nonneg h1] at hx
          omega
    · -- x + 5 < 0, i.e., x < -5
      by_cases h2 : x + 4 ≥ 0
      · -- x + 4 ≥ 0, i.e., x ≥ -4
        omega
      · -- x + 4 < 0, i.e., x < -4
        by_cases h3 : x + 2 ≥ 0
        · -- x + 2 ≥ 0, i.e., x ≥ -2
          rw [abs_of_nonneg h3, abs_of_neg (not_le.mp h2), abs_of_neg (not_le.mp h1)] at hx
          omega
        · -- x + 2 < 0, i.e., x < -2
          rw [abs_of_neg (not_le.mp h3), abs_of_neg (not_le.mp h2), abs_of_neg (not_le.mp h1)] at hx
          omega