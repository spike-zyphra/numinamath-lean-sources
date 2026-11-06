import Mathlib
theorem algebra_608404 (x y : ℝ) : (x - 2 * y) ^ 2 + (y - 1) ^ 2 = 0 ↔ x = 2 ∧ y = 1:= by
  constructor
  · -- Forward direction: equation to conjunction
    intro h
    have h1 : (x - 2 * y) ^ 2 ≥ 0:= by positivity
    have h2 : (y - 1) ^ 2 ≥ 0:= by positivity
    have h3 : (x - 2 * y) ^ 2 = 0:= by linarith
    have h4 : (y - 1) ^ 2 = 0:= by linarith
    have hy : y = 1:= by
      nlinarith
    have hx : x = 2 * y:= by
      nlinarith
    rw [hy] at hx
    constructor
    · -- Show x = 2
      linarith
    · -- Show y = 1
      exact hy
  · -- Backward direction: conjunction to equation
    rintro ⟨hx, hy⟩
    rw [hx, hy]
    norm_num