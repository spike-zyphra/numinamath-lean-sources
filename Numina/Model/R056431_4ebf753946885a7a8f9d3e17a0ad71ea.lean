import Mathlib

theorem number_theory_199004 {n : ℕ} :
    (n % 3 = 1 ∧ n^2 % 11 = 1 ∧ 100 < n ∧ n < 200) ↔
    n = 133 ∨ n = 166 ∨ n = 199 ∨ n = 109 ∨ n = 142 ∨ n = 175 := by
  constructor
  · -- Forward direction: if n satisfies the conditions, then n is one of the given numbers
    intro h
    rcases h with ⟨h1, h2, h3, h4⟩
    interval_cases n <;> norm_num at *
    <;> try { tauto }
  
  · -- Backward direction: if n is one of the given numbers, then it satisfies the conditions
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · -- n = 133
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- n = 166
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- n = 199
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- n = 109
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- n = 142
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- n = 175
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num