import Mathlib

theorem algebra_193525 (x y z : ℕ) (h : x + y + z = 96)
    (h1 : x = (0.8 : ℝ) * y) (h2 : z = (33.33 : ℝ) / 100 * (x + y)) :
    x = 40 ∧ y = 32 ∧ z = 24 := by
  have eq1 : (x : ℝ) + (y : ℝ) + (z : ℝ) = (96 : ℝ) := by
    exact_mod_cast h
  have eq2 : (x : ℝ) = (0.8 : ℝ) * (y : ℝ) := by
    simpa using h1
  have eq3 : (z : ℝ) = (33.33 : ℝ) / 100 * ((x : ℝ) + (y : ℝ)) := by
    simpa using h2
  have eq4 : (5 * (x : ℝ) = 4 * (y : ℝ)) := by
    have h2' : (x : ℝ) = (0.8 : ℝ) * (y : ℝ) := eq2
    ring_nf at h2' ⊢
    linarith
  have eq11 : (10000 * (z : ℝ) = (3333 : ℝ) * ((x : ℝ) + (y : ℝ))) := by
    have eq6' : (z : ℝ) = (33.33 / 100 : ℝ) * ((x : ℝ) + (y : ℝ)) := eq3
    ring_nf at eq6' ⊢
    linarith
  have eq12 : 5 * x = 4 * y := by
    have h9 : (5 * (x : ℝ) = 4 * (y : ℝ)) := eq4
    norm_cast at h9 ⊢
  have eq13 : 10000 * z = 3333 * (x + y) := by
    have h11 : (10000 * (z : ℝ) = (3333 : ℝ) * ((x : ℝ) + (y : ℝ)) ) := eq11
    norm_cast at h11 ⊢
  omega