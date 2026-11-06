import Mathlib

theorem algebra_9434 {m : ℝ} (h : ∃ c, ∀ x, m * x + m - 2 = c * x) :
    m = 2 := by
  rcases h with ⟨c, hc⟩
  have h0 := hc 0
  simp at h0
  linarith