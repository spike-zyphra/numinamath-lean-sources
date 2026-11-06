import Mathlib

theorem algebra_324407 {α : ℝ} (hα : α^2 + 3 * α - 2 = 0) (a : ℕ → ℝ)
    (h : ∀ x, (x^2 + 3 * x - 2) ∣ ∑ i ∈ Finset.range 7, a i * x^i) :
    ∑ i ∈ Finset.range 7, a i * α^i = 0 := by
  have h1 := h α
  rw [show α ^ 2 + 3 * α - 2 = (0 : ℝ) by linarith] at h1
  norm_num [Finset.sum_range_succ] at h1 ⊢
  all_goals norm_num [Finset.sum_range_succ] at h1 ⊢ <;> linarith