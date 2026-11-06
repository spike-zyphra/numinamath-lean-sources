import Mathlib

theorem algebra_21264 (Navin Luka Ian rupee kuna pula dollar : ℝ) (h1 : Navin = 160 * rupee) (h2 : Luka = 25 * kuna) (h3 : Ian = 34 * pula) (h4 : 0 < dollar) (h5 : dollar = 32.35 * rupee) (h6 : dollar = 5.18 * kuna) (h7 : dollar = 6.95 * pula) : IsGreatest {8 * Navin, 8 * Luka, 8 * Ian} (8 * Navin) := by
  constructor
  · -- Show that 8 * Navin is in the set
    simp [h1]
  · -- Show that 8 * Navin is greatest in the set
    intro x hx
    have h8 : x = 8 * Navin ∨ x = 8 * Luka ∨ x = 8 * Ian := by
      simp at hx
      tauto
    rcases h8 with (h8 | h8 | h8)
    · -- Case where x = 8 * Navin
      rw [h8]
      all_goals linarith
    · -- Case where x = 8 * Luka
      rw [h8]
      nlinarith [show (0 : ℝ) < dollar by linarith, h5, h6, h7]
    · -- Case where x = 8 * Ian
      rw [h8]
      nlinarith [show (0 : ℝ) < dollar by linarith, h5, h6, h7]