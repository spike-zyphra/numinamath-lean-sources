import Mathlib

theorem number_theory_608750: IsLeast {n: ℤ | 10 < n ∧ ∃ a b c d e f: ℤ, 0 ≤ a ∧ a ≤ 9 ∧ 0 ≤ b ∧ b ≤ 9 ∧
  0 ≤ c ∧ c ≤ 9 ∧ 0 ≤ d ∧ d ≤ 16 ∧ 0 ≤ e ∧ e ≤ 16 ∧ 0 ≤ f ∧ f ≤ 16 ∧
  n = 100 * a + 10 * b + c ∧ n = 289 * d + 17 * e + f ∧ a + b + c = d + e + f} 153:= by
  constructor
  · -- Show 153 is in the set.
    constructor
    · norm_num
    · -- Provide witnesses
      use 1, 5, 3, 0, 9, 0
      all_goals norm_num
  · -- Show 153 is the smallest.
    intro n hn
    rcases hn with ⟨hn10, ⟨a, b, c, d, e, f, ha0, ha9, hb0, hb9, hc0, hc9, hd0, hd16, he0, he16, hf0, hf16, h1, h2, h3⟩⟩
    by_contra h
    push_neg at h
    have h3' : n < 153 := by linarith
    rw [h1] at h3'
    have h4 : 100 * a + 10 * b + c < 153 := by linarith
    have ha0' : a ≤ 9 := by linarith
    have hb0' : b ≤ 9 := by linarith
    have hc0' : c ≤ 9 := by linarith
    -- Since all variables are bounded, we can use exhaustive search.
    have ha0_pos : 0 ≤ a := by linarith
    have hb0_pos : 0 ≤ b := by linarith
    have hc0_pos : 0 ≤ c := by linarith
    -- Since all variables are bounded, we can use exhaustive search.
    interval_cases a <;> interval_cases b <;> interval_cases c <;> omega