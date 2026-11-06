import Mathlib

theorem algebra_94346 {x : ℝ} (hx : x ≠ 0) (h : (1 - 12.5 / 100) * 24 * (1 + 33.33 / 100) = (x * (1 - 20 / 100))) :
    x ≠ 25.2 ∧ x ≠ 30 ∧ x ≠ 33.6 ∧ x ≠ 40 := by
  constructor
  · -- Show that x ≠ 25.2
    by_contra h1
    rw [show x = 25.2 by linarith [h1]] at h
    norm_num at h
  constructor
  · -- Show that x ≠ 30
    by_contra h2
    rw [show x = 30 by linarith [h2]] at h
    norm_num at h
  constructor
  · -- Show that x ≠ 33.6
    by_contra h3
    rw [show x = 33.6 by linarith [h3]] at h
    norm_num at h
  · -- Show that x ≠ 40
    by_contra h4
    rw [show x = 40 by linarith [h4]] at h
    norm_num at h