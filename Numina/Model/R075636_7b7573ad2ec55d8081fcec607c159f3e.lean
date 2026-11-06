import Mathlib

theorem algebra_217040 {L : ℝ} (hL : L > 0) (w_dwarves_S w_elves_S w_dwarves_D w_elves_D : ℝ)
    (hw_dwarves_S : w_dwarves_S = 1 + L / 3) (hw_elves_S : w_elves_S = 3 + L)
    (hw_dwarves_D : w_dwarves_D = 10 - 2 * L / 3) (hw_elves_D : w_elves_D = 18 - 2 * L)
    (h : w_dwarves_S * w_elves_D = w_elves_S * w_dwarves_D) :
    w_dwarves_S / w_elves_S = 2 := by
  rw [hw_dwarves_S, hw_elves_D, hw_elves_S, hw_dwarves_D] at h
  have h1 : (1 + L / 3) * (18 - 2 * L) = (3 + L) * (10 - 2 * L / 3) := by
    nlinarith
  have h2 : L < 0 := by 
    nlinarith [sq_nonneg (L + 3)]
  linarith