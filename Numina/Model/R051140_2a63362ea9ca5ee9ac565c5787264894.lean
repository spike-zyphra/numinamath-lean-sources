import Mathlib

theorem number_theory_12932 (l w h : ℕ) (hw : w = l - 5) (hw' : h = w - 5)
    (hvol : l * w * h > 2019) (hvol' : 13 ∣ l * w * h + 3) :
    l ≥ 20 := by
  rw [hw] at hw'
  rw [hw'] at hvol hvol'
  by_contra h'
  push_neg at h'
  interval_cases l <;> norm_num [hw, hw'] at hvol hvol' <;> omega