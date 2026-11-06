import Mathlib

theorem other_176222 (m_B : ℝ) (h_B : m_B > 0) (h : 50 * 2100 * (-10) + m_B * 4200 * 10 = 0)
    (h' : 50 * 3300 + m_B * 4200 = 0) :
    0.0028 ≤ m_B ∧ m_B ≤ 0.418 := by
  exfalso
  nlinarith
  all_goals exfalso
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith