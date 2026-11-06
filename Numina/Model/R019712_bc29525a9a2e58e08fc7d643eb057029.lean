import Mathlib

theorem algebra_253508 {f : ℝ → ℝ} (h : ∀ x y z, f (x * y) + f (x * z) - 2 * f x * f (y * z) ≥ 1 / 2) :
    ∑ i ∈ Finset.range 2022, ⌊(i + 1) * f (i + 1)⌋ = 1022121 := by
  have h1 : f 0 = 1 / 2 := by
    have h0 := h 0 0 0 
    norm_num at h0
    nlinarith [sq_nonneg (f 0 - 1 / 2)]
  have h2 : f 1 = 1 / 2 := by
    have h0 := h 1 1 1 
    norm_num at h0 
    nlinarith [sq_nonneg (f 1 - 1 / 2)]
  have h3 : ∀ (X : ℝ), f X = 1 / 2 := by 
    intro X
    have h4 := h X 1 1 
    have h5 := h X 0 0 
    norm_num [show f 1 = 1 / 2 by linarith [h2]] at h4 
    norm_num [show f 0 = 1 / 2 by linarith [h1]] at h5 
    linarith 
  -- Therefore, we can compute the sum.
  have h4 : ∀ (i : ℕ), ⌊(↑i + 1) * f (↑i + 1)⌋ = ⌊(↑i + 1) * (1 / 2 : ℝ)⌋ := by
    intro i 
    have h5 : f (↑i + 1 : ℝ) = 1 / 2 := h3 (↑i + 1 : ℝ)
    simp [h5] 
  rw [show ∑ i ∈ Finset.range 2022, ⌊(↑i + 1) * f (↑i + 1)⌋ = ∑ i ∈ Finset.range 2022, ⌊(↑i + 1) * (1 / 2 : ℝ)⌋ by 
    apply Finset.sum_congr 
    · rfl 
    · intro i hi 
      specialize h4 i 
      simpa using h4
  ]
  norm_num [Finset.sum_range_succ]