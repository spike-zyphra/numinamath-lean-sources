import Mathlib

theorem algebra_11339 : IsGreatest { a * b | (a : ℤ) (b : ℤ) (_ : a > 0) (_ : b > 0) (h : 2 * (a + b) = 30) } 56 := by
  constructor
  · -- Show 56 is in the set
    use 7, 8
    all_goals norm_num
  · -- Show 56 is greatest in the set
    intro z h
    rcases h with ⟨a, b, ha, hb, h1, h2⟩
    have h3 : a + b = 15 := by
      linarith
    have h4 : b = 15 - a := by
      omega
    have h5 : z = a * (15 - a) := by
      rw [show b = 15 - a by omega] at h2
      linarith
    have h6 : a ≤ 14 := by
      nlinarith [h3, hb]
    have h7 : a ≥ 1 := by
      omega
    have h8 : z ≤ 56 := by
      rw [h5]
      interval_cases a <;> omega
    linarith