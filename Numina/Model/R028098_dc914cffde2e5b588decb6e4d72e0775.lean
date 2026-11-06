import Mathlib

theorem algebra_22653 (f : ℝ → ℝ) (hf : Set.range f = {x | x ∈ Set.Icc (-3) 5}) :
    Set.range (fun x => (f x)^2) = {x | x ∈ Set.Icc 0 25} := by
  ext y
  simp only [Set.mem_range, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- Assume y is in the range of (f x)^2
    rintro ⟨x, hx⟩
    have hy : f x ∈ Set.Icc (-3 : ℝ) 5 := by
      have h1 : f x ∈ Set.range f := by
        simpa using ⟨x, by linarith⟩
      rw [hf] at h1
      exact h1
    rcases hy with ⟨h1, h2⟩
    constructor
    · -- Show 0 ≤ (f x)^2
      nlinarith [sq_nonneg (f x)]
    · -- Show (f x)^2 ≤ 25
      nlinarith [sq_nonneg (f x - 5), sq_nonneg (f x + 3)]
  · -- Now prove the reverse direction
    rintro ⟨hy1, hy2⟩
    have h5 : Real.sqrt y ∈ Set.Icc (-3 : ℝ) 5 := by
      constructor
      · -- Show -3 ≤ √y
        have h1 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
        linarith
      · -- Show √y ≤ 5
        have h2 : Real.sqrt y ≤ 5 := by
          nlinarith [Real.sqrt_nonneg y, Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), hy2]
        linarith
    -- Because √y is in the range of f, by hypothesis
    have h5 : ∃ r, f r = Real.sqrt y := by
      have h1 : Real.sqrt y ∈ Set.range f := by
        rw [hf] at *
        exact h5
      rcases h1 with ⟨r, hr⟩
      exact ⟨r, hr⟩
    rcases h5 with ⟨r, hr⟩
    use r
    have eq1 : (f r) ^ 2 = y := by
      rw [hr]
      rw [Real.sq_sqrt]
      all_goals nlinarith
    linarith [eq1]