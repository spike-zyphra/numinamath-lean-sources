import Mathlib

theorem algebra_114977 (r : ℕ) (hr : r > 0) (a : ℕ → ℝ)
    (h1 : ∀ i, i + 1 < r → i + 2 < r → a i + a (i + 1) + a (i + 2) < 0)
    (h2 : ∀ i, i + 1 < r → i + 2 < r → i + 3 < r → a i + a (i + 1) + a (i + 2) + a (i + 3) > 0) :
    r ≤ 5 := by
  by_contra h
  push_neg at h
  have h1_0 := h1 0 (by linarith) (by linarith)
  have h1_1 := h1 1 (by linarith) (by linarith)
  have h1_2 := h1 2 (by linarith) (by linarith)
  have h1_3 := h1 3 (by linarith) (by linarith)
  have h2_0 := h2 0 (by linarith) (by linarith) (by linarith)
  have h2_1 := h2 1 (by linarith) (by linarith) (by linarith)
  have h2_2 := h2 2 (by linarith) (by linarith) (by linarith)
  norm_num at h1_0 h1_1 h1_2 h1_3 h2_0 h2_1 h2_2
  linarith