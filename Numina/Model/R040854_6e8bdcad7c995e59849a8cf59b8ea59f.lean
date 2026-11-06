import Mathlib

theorem algebra_13575 {f : ℤ → ℤ} (h : ∀ m n, f (m + n) + f (m * n - 1) = f m * f n + 2) :
    ∃(S : Finset ℤ), S = {y | y = f 2} ∧ S.card * (∑ y ∈ S, y) = 5 := by 
  have h1 := h 0 0
  have h2 := h 1 1
  have h3 := h 2 0
  have h4 := h 1 (-1)
  have h5 := h (-1) (-1)
  have h6 := h 0 (-1)
  simp at h1 h2 h3 h4 h5 h6
  have h7 : f 0 = 1 := by
    nlinarith [h1, h6]
  have h8 : f (-1) = 2 := by
    nlinarith [h6, h7]
  have h9 : f (-2) = 5 := by
    nlinarith [h5, h7, h8]
  have h10 : f 1 = 2 := by
    nlinarith [h4, h7, h8, h9]
  have h11 : f 2 = 5 := by
    nlinarith [h2, h7, h10]
  use {5}
  constructor
  · -- Show that {5} = {y | y = f 2}
    ext y
    simp [h11]
    all_goals omega
  · -- Show that {5}.card * ∑ y ∈ {5}, y = 5
    simp
    all_goals linarith