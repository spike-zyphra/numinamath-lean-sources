import Mathlib

theorem algebra_206987 {x y z : ℝ} (hx : x = 1) (hy : y = 0.2) (hz : z = 2.1) :
    x + ⌊y⌋ + (z - ⌊z⌋) = 1.1 ∧
    (x - ⌊x⌋) + y + ⌊z⌋ = 2.2 ∧
    ⌊x⌋ + (y - ⌊y⌋) + z = 3.3 := by
  rw [hx, hy, hz]
  constructor
  · -- Check the first equation
    norm_num [Int.floor_eq_iff]
  constructor
  · -- Check the second equation
    norm_num [Int.floor_eq_iff]
  · -- Check the third equation
    norm_num [Int.floor_eq_iff]