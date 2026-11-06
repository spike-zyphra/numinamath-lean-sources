import Mathlib

theorem number_theory_228424 {x : ℕ} (hx : x % 8 = 7) (hxp : x / 6 = x / 8 + 8) (hxp' : x % 6 = 2)
    (hxp'' : x / 5 = x / 6 + 5) : x = 175 := by
  omega