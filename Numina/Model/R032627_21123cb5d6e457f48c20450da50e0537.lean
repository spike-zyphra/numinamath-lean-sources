import Mathlib

theorem other_61419 (a : ℝ) (f : ℝ → ℝ) (h0 : f 0 = 1 / 2)
    (hadd : ∀ x y, f (x + y) = f x * f (a - y) + f y * f (a - x)) :
    ∃ c, ∀ x, f x = c := by

  have ha : f a = 1 / 2 := by
    specialize hadd 0 0
    rw [show (0 : ℝ) + (0 : ℝ) = (0 : ℝ) by ring] at hadd
    have eq1 : f 0 * f (a - (0 : ℝ)) + f 0 * f (a - (0 : ℝ)) = 2 * (f 0 * f a) := by
      simp [show a - (0 : ℝ) = a by ring]
      <;> ring
    rw [eq1] at hadd
    rw [h0] at hadd
    linarith

  have h1 : ∀ x, f x = f (a - x) := by
    intro x
    specialize hadd x 0
    have eq1 : f (x + (0 : ℝ)) = f x := by
      simp
    rw [eq1] at hadd
    simp [show a - (0 : ℝ) = a by ring, h0, ha] at hadd
    linarith

  have h2 : ∀ x, f x ^ 2 = 1 / 4 := by
    intro x
    specialize hadd x (a - x)
    have eq1 : x + (a - x) = a := by 
      ring
    rw [eq1] at hadd
    have eq2 : f (a - (a - x)) = f x := by
      rw [show a - (a - x) = x by ring]
    rw [eq2] at hadd
    have eq3 : f (a - x) = f x := by
      linarith [h1 x]
    rw [eq3] at hadd
    nlinarith [ha]

  have h3 : ∀ x y, f (x + y) = 2 * (f x * f y) := by
    intro x y
    specialize hadd x y
    have eq1 : f (a - y) = f y := by
      specialize h1 y
      linarith
    have eq2 : f (a - x) = f x := by
      specialize h1 x
      linarith
    rw [eq1, eq2] at hadd
    nlinarith

  have h4 : ∀ x, f (2 * x) = 1 / 2 := by 
    intro x
    specialize h3 x x
    have eq1 : (x + x : ℝ) = 2 * x := by ring
    rw [eq1] at h3
    have h5 : f x ^ 2 = 1 / 4 := by
      apply h2
    nlinarith

  use 1 / 2
  intro x
  have eq1 : f (2 * (x / 2)) = 1 / 2 := by
    specialize h4 (x / 2)
    ring_nf at h4 ⊢
    linarith
  have eq2 : 2 * (x / 2) = x := by ring
  rw [eq2] at eq1
  linarith