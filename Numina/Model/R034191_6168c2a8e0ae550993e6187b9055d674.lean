import Mathlib

theorem algebra_182045 (d : ℝ) (h : d = 525) (v1 v2 : ℝ)
    (h1 : v1 = 82) (h2 : v2 = 63) (t : ℝ) (ht : t = 6) :
    dist (v1 * t) (v2 * t) = 114 ∧
    d - v1 * t = 33 ∧
    d - v2 * t = 147 := by

  have h3 : v1 * t = 492 := by
    rw [h1, ht]
    norm_num

  have h4 : v2 * t = 378 := by
    rw [h2, ht]
    norm_num

  have h5 : dist (v1 * t) (v2 * t) = 114 := by
    rw [h3, h4]
    norm_num [dist]

  have h6 : d - v1 * t = 33 := by
    rw [h, h3]
    norm_num

  have h7 : d - v2 * t = 147 := by
    rw [h, h4]
    norm_num

  constructor
  · exact h5
  constructor
  · exact h6
  · exact h7