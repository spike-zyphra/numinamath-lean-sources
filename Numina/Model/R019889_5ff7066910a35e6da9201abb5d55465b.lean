import Mathlib

theorem algebra_292929 (f : ℝ → ℝ) (h : ∀ x y z, (1 / 3) * f (x * y) + (1 / 3) * f (x * z) - f x * f (y * z) ≥ 1 / 9) :
    ∑ i ∈ Finset.range 100, ⌊(i + 1) * f (i + 1)⌋ = 1650 := by
  have h1 : f 0 = 1 / 3 := by
    specialize h 0 0 0
    simp at h
    nlinarith [sq_nonneg (f 0 - 1 / 3)]

  have h2 : f 1 = 1 / 3 := by 
    specialize h 1 1 1
    norm_num at h 
    nlinarith [sq_nonneg (f 1 - 1 / 3)]

  have h3 : ∀ x : ℝ, f x = 1 / 3 := by 
    intro x
    have hx1 := h x 1 1
    have hx2 := h x (0 : ℝ) (0 : ℝ)
    simp [show f 1 = 1 / 3 by linarith [h2], h1] at hx1 hx2
    linarith

  have h4 : ∀ (i : ℕ), (i + 1 : ℝ) * f (i + 1 : ℝ) = (i + 1 : ℝ) / 3 := by 
    intro i
    specialize h3 (i + 1 : ℝ)
    simp [h3] 
    <;> linarith

  have h5 : ∀ (i : ℕ), ⌊(i + 1 : ℝ) * f (i + 1 : ℝ)⌋ = ⌊(i + 1 : ℝ) / 3⌋ := by 
    intro i
    rw [h4 i]

  rw [Finset.sum_congr rfl (fun i _ => h5 i)]

  norm_num [Finset.sum_range_succ, h3]