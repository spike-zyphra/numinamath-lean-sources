import Mathlib

theorem algebra_110052 {f : ℝ → ℝ} (h1 : ∀ x, f (x + 3) = f (3 - x)) (h2 : ∀ x, f (x + 11) = f (11 - x)) :
    ∃ c, 0 < c ∧ Function.Periodic f c := by
  use 16
  constructor
  · -- Show that 16 is positive
    norm_num
  · -- Show that f is periodic with period 16
    unfold Function.Periodic
    intro x
    have h3 : ∀ t, f t = f (6 - t) := by
      intro t
      have eq1 := h1 (t - 3)
      have eq2 : f ((t - 3 : ℝ) + 3) = f (3 - (t - 3 : ℝ)) := by
        simpa using eq1
      have eq3 : (t - 3 : ℝ) + 3 = (t : ℝ) := by ring
      have eq4 : (3 - (t - 3 : ℝ)) = (6 - t : ℝ) := by ring
      rw [eq3, eq4] at eq2
      linarith [eq2]
    have h4 : ∀ t, f t = f (22 - t) := by
      intro t
      have eq1 := h2 (t - 11)
      have eq2 : f ((t - 11 : ℝ) + 11) = f (11 - (t - 11 : ℝ)) := by
        simpa using eq1
      have eq3 : (t - 11 : ℝ) + 11 = (t : ℝ) := by ring
      have eq4 : (11 - (t - 11 : ℝ)) = (22 - t : ℝ) := by ring
      rw [eq3, eq4] at eq2
      linarith [eq2]
    have h5 : ∀ t, f (t + 16) = f t := by
      intro t
      have eq1 : f (t + 16) = f (6 - t) := by
        have eq2 : f (t + 16) = f (22 - (t + 16 : ℝ)) := by
          rw [h4 (t + 16)]
        have eq4 : (22 - (t + 16 : ℝ)) = (6 - t : ℝ) := by ring
        rw [eq4] at eq2
        linarith [eq2]
      have eq3 : f (6 - t) = f t := by
        have eq4 : f t = f (6 - t) := by
          linarith [h3 t]
        linarith [eq4]
      linarith [eq1, eq3]
    specialize h5 x
    simpa using h5