import Mathlib

theorem algebra_324305 {f : ℝ → ℝ}
    (h : ∀ x y z, (1 / 2) * f (x * y) + (1 / 2) * f (x * z) - f x * f (y * z) ≥ 1 / 4) :
    ∑ i ∈ Finset.range 2011, ⌊(i + 1) * f (i + 1)⌋ = 1011030 := by

  have h1 : f 0 = 1 / 2 := by
    have h1 := h 0 0 0
    norm_num at h1
    have h2 := h 0 1 0
    norm_num at h2
    nlinarith [sq_nonneg (f 0 - 1 / 2)]

  have h2 : f 1 = 1 / 2 := by
    have h1 := h 1 1 1
    norm_num at h1
    have h4 := h 1 0 0
    norm_num [h1] at h4
    nlinarith [sq_nonneg (f 1 - 1 / 2)]

  have h3 : ∀ x : ℝ, f x = 1 / 2 := by
    intro x 
    have h4 := h x 0 0
    simp [h1] at h4 
    have h5 := h x 1 1 
    norm_num [h2] at h5
    have h6 : f x = 1 / 2 := by
      nlinarith
    exact h6

  have h5 : ∀ (i : ℕ), ⌊(i + 1 : ℝ) * f (i + 1 : ℝ)⌋ = ⌊(i + 1 : ℝ) * (1 / 2 : ℝ)⌋ := by
    intro i
    have h6 : f (i + 1 : ℝ) = (1 / 2 : ℝ) := h3 (i + 1 : ℝ)
    rw [h6]

  have h5' : ∑ i ∈ Finset.range 2011, ⌊(i + 1) * f (i + 1)⌋ = ∑ i ∈ Finset.range 2011, ⌊(i + 1 : ℝ) * (1 / 2 : ℝ)⌋ := by
    congr
    all_goals
      funext i
      have h6 : f (i + 1 : ℝ) = (1 / 2 : ℝ) := h3 (i + 1 : ℝ)
      rw [h6]

  rw [h5']
  norm_num [Finset.sum_range_succ, Int.floor_eq_iff, h3]