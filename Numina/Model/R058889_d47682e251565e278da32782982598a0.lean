import Mathlib

/- # Task № 2

The captain's assistant, observing the loading of the ship, smoked one pipe after another from the start of the loading. When $2 / 3$ of the number of loaded containers became equal to $4 / 9$ of the number of unloaded containers, and the ship's bells struck noon, the old seafarer began to light another pipe. When he finished smoking it, the ratio of the number of loaded containers to the number of unloaded containers became the inverse of the ratio that existed before he started smoking that pipe. How many pipes did the second assistant smoke during the loading (assuming that the loading speed, as well as the smoking speed, remained constant throughout the process.) -/
theorem algebra_138656 {x : ℕ} (hx : x > 0) (h : (2 / 3 : ℚ) * x = (4 / 9 : ℚ) * (x - 2)) :
    x = 5 := by
  have h1 : (x : ℚ) > (0 : ℚ) := by exact_mod_cast hx
  have eq1 : (x : ℚ) = 5 := by
    linarith
  exact_mod_cast eq1