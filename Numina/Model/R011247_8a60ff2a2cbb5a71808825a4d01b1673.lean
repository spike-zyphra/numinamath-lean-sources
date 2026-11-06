import Mathlib


theorem number_theory_631204 : IsLeast {n : ℕ | ∃ a b : ℕ, a ≤ 100 ∧ b ≤ 100 ∧ n = a + b ∧ Real.sqrt 15 < (a / b : ℝ) ∧ (a / b : ℝ) < 4} 39 := by
  constructor
  · -- Show that 39 is in the set
    use 31, 8
    constructor
    · norm_num -- a ≤ 100
    constructor
    · norm_num -- b ≤ 100
    constructor
    · norm_num -- n = a + b
    constructor
    · -- Show that Real.sqrt 15 < (31 / 8 : ℝ)
      have h1 : Real.sqrt 15 < (31 / 8 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      exact_mod_cast h1
    · -- Show that (31 / 8 : ℝ) < 4
      norm_num
  · -- Show that 39 is the least element in the set
    intro n hn
    rcases hn with ⟨a, b, ha, hb, hn, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : a + b < 39 := by
      omega
    have h4 : a ≤ 38 := by
      omega
    have h5 : b ≤ 38 := by
      omega
    interval_cases b <;> try { 
      interval_cases a <;> norm_num [Real.sqrt_lt, Real.lt_sqrt] at h1 h2 <;> norm_num at *
    }