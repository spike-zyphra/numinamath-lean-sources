import Mathlib

theorem algebra_19551 : IsLeast {n : ℤ | ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ a ≠ b ∧ a * b = 3 * (2 * (a + b)) ∧ n = 2 * (a + b)} 50 := by
  constructor
  · -- First proof: 50 is obtainable from (10, 15)
    use 10, 15
    all_goals norm_num
  · -- Now proving that 50 is the minimal
    intro n hn
    rcases hn with ⟨a, b, ha, hb, hneq, heq, hn⟩
    have eq1 : a * b = 6 * (a + b) := by
      linarith
    by_contra h
    push_neg at h
    have h2 : n < 50 := by linarith
    have h1 : a + b < 25 := by
      linarith [hn, h2]
    have h3 : a ≤ 24 := by
      nlinarith
    have h4 : b ≤ 24 := by
      nlinarith
    interval_cases a <;> interval_cases b
    <;> norm_num at ha hb hneq eq1 hn
    <;> omega