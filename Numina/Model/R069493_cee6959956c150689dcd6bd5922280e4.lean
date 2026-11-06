import Mathlib

open Real

theorem calculus_66361 (f : ℕ → ℝ) (hf : f 0 = 2) (h : ∀ n, f (n + 1) = f n * (2 / 3)) :
    ∃ n, f n < 1 / 6 := by
  have h1 : f 0 = 2 := hf
  have h2 : f 1 = f 0 * (2 / 3) := h 0
  rw [h1] at h2
  norm_num at h2

  have h3 : f 2 = f 1 * (2 / 3) := h 1
  rw [h2] at h3
  norm_num at h3

  have h4 : f 3 = f 2 * (2 / 3) := h 2
  rw [h3] at h4
  norm_num at h4

  have h5 : f 4 = f 3 * (2 / 3) := h 3
  rw [h4] at h5
  norm_num at h5

  have h6 : f 5 = f 4 * (2 / 3) := h 4
  rw [h5] at h6
  norm_num at h6

  have h7 : f 6 = f 5 * (2 / 3) := h 5
  rw [h6] at h7
  norm_num at h7

  have h8 : f 7 = f 6 * (2 / 3) := h 6
  rw [h7] at h8
  norm_num at h8

  have h9 : f 7 < 1 / 6 := by
    linarith

  exact ⟨7, h9⟩