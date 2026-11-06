import Mathlib

theorem algebra_269757 (megan_inheritance dan_inheritance : ℝ)
    (hmegan_inheritance : megan_inheritance = 1000000) (hdan_inheritance : dan_inheritance = 10000) :
    (megan_inheritance * 0.1) + (dan_inheritance * 0.1) = 101000 := by
  rw [hmegan_inheritance, hdan_inheritance]
  norm_num