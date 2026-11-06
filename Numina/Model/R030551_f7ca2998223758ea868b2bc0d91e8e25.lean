import Mathlib

theorem algebra_234016 {g : ℝ → ℝ} (h : ∀ x y, g (x - y) = g x + g y - 2021 * (x + y)) :
    g 2022 = 4086462 := by

  have h0 : g 0 = 0 := by
    specialize h 0 0
    norm_num at h
    linarith

  have eq1 : ∀ x : ℝ, g x = 2021 * x := by
    intro x
    have eq2 := h x x
    have eq3 : g (x - x) = g x + g x - 2021 * (x + x) := by 
      simpa using eq2
    have eq4 : g (x - x) = g 0 := by
      simp
    rw [eq4, h0] at eq3
    linarith

  have eq2 : g 2022 = 2021 * (2022 : ℝ) := by
    specialize eq1 2022
    simpa using eq1

  rw [eq2]
  norm_num