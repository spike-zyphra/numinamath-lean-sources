import Mathlib

theorem intermediate_algebra_4101 {f : ℝ → ℝ} (h : f 1 = 1) (h' : ∀ x y, f (x + y) = 3 ^ y * f x + 2 ^ x * f y) :
    ∀ x, f x = 3 ^ x - 2 ^ x := by
  have h0 : f 0 = 0 := by
    specialize h' 0 0
    norm_num at h'
    linarith
  intro x
  have eq1 := h' x 1
  have eq2 := h' 1 x
  have eq3 : f (x + 1) = 3 * f x + (2 : ℝ) ^ x := by
    specialize h' x 1
    rw [show (x + (1 : ℝ)) = x + (1 : ℝ) by ring] at h'
    norm_num [h] at h'
    linarith
  have eq4 : f (1 + x) = (3 : ℝ) ^ x + 2 * f x := by
    specialize h' 1 x
    rw [show (1 + x : ℝ) = (1 : ℝ) + x by ring] at *
    norm_num [h] at h'
    linarith
  have eq8 : f x = (3 : ℝ) ^ x - (2 : ℝ) ^ x := by
    have h8 : f (x + 1) = f (1 + x) := by ring_nf
    rw [eq3] at h8
    rw [eq4] at h8
    linarith
  simpa using eq8