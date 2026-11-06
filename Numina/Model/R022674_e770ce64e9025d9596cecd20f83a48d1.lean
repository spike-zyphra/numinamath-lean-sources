import Mathlib

theorem number_theory_107734 (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (h : 13 * a + 65 * b + 289 * c = 6622) (h1 : a < b) (h2 : b < c) :
    a = 2 ∧ b = 17 ∧ c = 19 := by
  have h3 : c ≤ 23 := by
    by_contra h4
    push_neg at h4
    have : 289 * c ≥ 289 * 24 := by
      nlinarith
    omega
  have h4 : c % 13 = 6 := by
    omega
  have h5 : c = 19 := by
    interval_cases c <;> norm_num at hc h4 h <;> omega
  rw [h5] at h
  have h6 : a + 5 * b = 87 := by
    omega
  have h7 : a ≤ 87 := by 
    omega
  have h8 : b ≤ 17 := by
    omega
  interval_cases b <;> norm_num at hb h6 h <;> interval_cases a <;> norm_num at ha h6 h <;> tauto