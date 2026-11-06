import Mathlib

theorem number_theory_194795 (a b : ℕ) (ha : a < 10) (hb : b > 0)
    (h : 111000 + 100 * a + 10 * a + a = b * (b + 1)) :
    b = 333 := by
  have h1 : b ≤ 334 := by
    nlinarith [h, ha]
  have h2 : b ≥ 333 := by
    nlinarith [h, ha]
  have h3 : b = 333 ∨ b = 334 := by 
    omega
  rcases h3 with (rfl | rfl)
  · -- b = 333
    all_goals omega
  · -- b = 334
    exfalso
    -- Show that a must be at least 10, contradicting a < 10
    omega