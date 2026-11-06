import Mathlib

theorem algebra_300346 {f : ℝ → ℝ}
    (h : ∀ x y, f (4 * x - y - 1) + 4 * f (x + y) - 16 * f x = (6 * x - 2) ^ 2 + 45 * y ^ 2) :
    ∀ x, f x = (3 * x - 1) ^ 2 := by

  intro x
  have eq1 := h x 0
  have eq3 : f (4 * x - (0 : ℝ) - 1) + 4 * f (x + (0 : ℝ)) - 16 * f x = (6 * x - 2) ^ 2 + 45 * (0 : ℝ) ^ 2 := by 
    simpa using eq1
  have eq4 : f (4 * x - (0 : ℝ) - 1) = f (4 * x - 1) := by 
    ring_nf
  have eq5 : f (x + (0 : ℝ)) = f x := by 
    ring_nf
  rw [eq4, eq5, show (0 : ℝ) ^ 2 = 0 by ring] at eq3

  have eq2 := h x (3 * x - 1)
  have eq6 : f (4 * x - (3 * x - 1) - 1) + 4 * f (x + (3 * x - 1)) - 16 * f x = (6 * x - 2) ^ 2 + 45 * (3 * x - 1) ^ 2 := by 
    simpa using eq2
  have eq7 : f (4 * x - (3 * x - 1) - 1) = f x := by 
    ring_nf
  have eq8 : f (x + (3 * x - 1)) = f (4 * x - 1) := by 
    ring_nf
  rw [eq7, eq8] at eq6

  have eq8 : f (4 * x - 1) = (6 * x - 2) ^ 2 + 12 * f x := by
    linarith [eq3]

  rw [eq8] at eq6

  have eq9 : (6 * x - 2) ^ 2 = 4 * (3 * x - 1) ^ 2 := by
    ring_nf

  have eq10 : 3 * (6 * x - 2) ^ 2 + 33 * f x = 45 * (3 * x - 1) ^ 2 := by
    nlinarith

  rw [eq9] at eq10

  have eq11 : 33 * f x = 33 * (3 * x - 1) ^ 2 := by
    nlinarith

  have eq12 : f x = (3 * x - 1) ^ 2 := by
    nlinarith

  exact eq12