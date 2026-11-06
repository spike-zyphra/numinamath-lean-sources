import Mathlib

theorem calculus_13236 (a c : ℝ) (h : (crossProduct ![a, -1, c]) ![7, 3, 5] = ![-11, -16, 25]) :
    a = 6 ∧ c = 2 := by
  have h1 := congr_arg (λ v => v 0) h
  have h2 := congr_arg (λ v => v 1) h
  have h3 := congr_arg (λ v => v 2) h
  simp [crossProduct] at h1 h2 h3
  have hc : c = 2 := by
    linarith
  have ha : a = 6 := by
    rw [hc] at h2
    linarith
  constructor
  · exact ha
  · exact hc