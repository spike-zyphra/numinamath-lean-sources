import Mathlib

/-A world-record swimmer and a dolphin compete in a 400-meter race. The swimmer swims at a rate of 2 meters per second, and the dolphin swims at a rate of 8 meters per second. When the dolphin crosses the finish line, how many meters is the swimmer from the finish line?-/
theorem algebra_4412 (d t : ℝ) (ht : d / t = 8) (hd : d = 400) :
    400 - (2 * t) = 300 := by
  -- first show that t = 50
  replace ht : t = 50 := by
    rw [hd] at ht
    -- we must have t ≠ 0
    have ht0 : t ≠ 0 := by
      intro h
      rw [h] at ht
      norm_num at ht
    field_simp at ht
    linarith only [ht]
  -- get the answer
  rw [ht]
  norm_num