import Mathlib.Tactic

theorem alg_1208
  (can room : ℕ)
  (three_cans_eq_five_rooms : (3 : ℚ) * can = 5 * room) :
  (15 : ℚ) * can = 25 * room := by
    have h1 : (3 : ℚ) * (can : ℚ) = (5 : ℚ) * (room : ℚ) := by
      exact_mod_cast three_cans_eq_five_rooms
    have h2 : (15 : ℚ) * (can : ℚ) = (25 : ℚ) * (room : ℚ) := by
      linarith
    exact_mod_cast h2