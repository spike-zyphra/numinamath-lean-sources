import Mathlib

theorem algebra_140235 {f : ℝ → ℝ} (h : ∀ x, f (Real.sin x + 1) = (Real.cos x)^2 + Real.sin x - 3)
    (x : ℝ) (hx : x ∈ Set.Icc 0 2) :
    f x = -x^2 + 3 * x - 4 := by
  have h1 : 0 ≤ x := by
    have h1 : x ∈ Set.Icc (0 : ℝ) 2 := hx
    simp at h1 ⊢
    linarith
  have h2 : x ≤ 2 := by
    have h1 : x ∈ Set.Icc (0 : ℝ) 2 := hx
    simp at h1 ⊢
    linarith
  have h4 : ∃ y, Real.sin y = x - 1 := by
    use Real.arcsin (x - 1)
    have h5 : Real.sin (Real.arcsin (x - 1)) = x - 1 := by
      apply Real.sin_arcsin
      all_goals linarith
    linarith
  rcases h4 with ⟨y, hy⟩
  have h5 : Real.sin y = x - 1 := hy
  have h6 : Real.sin y + 1 = x := by
    linarith
  have h7 : f x = (Real.cos y) ^ 2 + Real.sin y - 3 := by
    calc 
      f x = f (Real.sin y + 1) := by rw [h6]
      _   = (Real.cos y) ^ 2 + Real.sin y - 3 := by
        apply h y
  have h8 : (Real.cos y) ^ 2 = 1 - (Real.sin y) ^ 2 := by
    rw [Real.cos_sq']
    <;> nlinarith
  rw [h7]
  rw [h8, hy]
  all_goals nlinarith