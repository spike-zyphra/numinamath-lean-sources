import Mathlib

theorem algebra_12028 {f : ℝ → ℝ} (h0 : f 0 = 1) (h : ∀ x y, f (x * y) = f ((x ^ 2 + y ^ 2) / 2) + (x - y) ^ 2) :
    ∀ x, f x = 1 - 2 * x := by
  have h1 : ∀ t, f (t ^ 2 / 2) = 1 - t ^ 2 := by
    intro t
    have h2 := h t 0
    simp at h2
    rw [h0] at h2
    linarith
  intro x
  have h3 := h x 1
  have h4 : f x = f ((x ^ 2 + 1) / 2) + (x - 1) ^ 2 := by
    norm_num at h3 ⊢
    linarith
  have h7 : f ((x ^ 2 + 1) / 2) = -x ^ 2 := by
    have h8 : ∃ t : ℝ, t ^ 2 = x ^ 2 + 1 := by
      use Real.sqrt (x ^ 2 + 1)
      rw [Real.sq_sqrt]
      positivity
    rcases h8 with ⟨t, ht⟩
    have h9 : f (t ^ 2 / 2) = 1 - t ^ 2 := h1 t
    have h10 : t ^ 2 / 2 = (x ^ 2 + 1) / 2 := by
      rw [ht]
      all_goals linarith
    rw [h10] at h9
    have h11 : 1 - t ^ 2 = -x ^ 2 := by
      nlinarith [ht]
    linarith
  rw [h7] at h4
  nlinarith