import Mathlib

theorem algebra_247453 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x * f y) (h' : f 1 = 2) :
    ∑ i ∈ Finset.range 1000, f (2 * i + 2) / f (2 * i + 1) = 2000 := by
  have h1 : f 0 = 1 := by
    have h2 : f 0 = f 0 * f 0 := by 
      specialize h 0 0
      norm_num at h ⊢
      linarith
    have h3 : f 0 * (f 0 - 1) = 0 := by 
      linarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case f 0 = 0.
      have h7 : f 1 = 0 := by
        specialize h 1 0
        norm_num at h ⊢
        rw [h4] at h
        linarith
      linarith [h7, h']
    · -- Case f 0 - 1 = 0.
      linarith
  have h2 : ∀ x : ℝ, f x ≠ 0 := by
    intro x
    by_contra hx
    have h3 : f 1 = 0 := by
      have h4 : f 1 = f x * f (1 - x) := by
        specialize h x (1 - x)
        have h5 : x + (1 - x) = 1 := by ring
        rw [h5] at h
        linarith
      rw [hx] at h4
      norm_num at h4 ⊢
      all_goals
        linarith
    linarith [h3, h']
  have h3 : ∀ i : ℕ, f (2 * (i : ℝ) + 2) / f (2 * (i : ℝ) + 1) = 2 := by
    intro i
    have eq1 : f (2 * (i : ℝ) + 2) = f (2 * (i : ℝ) + 1) * f 1 := by
      specialize h (2 * (i : ℝ) + 1) 1
      have h4 : (2 * (i : ℝ) + 1 : ℝ) + (1 : ℝ) = (2 * (i : ℝ) + 2 : ℝ) := by ring
      rw [h4] at h
      linarith
    have eq3 : f (2 * (i : ℝ) + 1) ≠ 0 := by
      apply h2
    have eq4 : f (2 * (i : ℝ) + 2) = f (2 * (i : ℝ) + 1) * 2 := by
      rw [eq1]
      rw [h']
    rw [eq4]
    field_simp [eq3]
    <;> nlinarith
  have h5 : ∑ i in Finset.range 1000, f (2 * i + 2) / f (2 * i + 1) = 1000 * 2 := by
    have h6 : ∀ i : ℕ, f (2 * (i : ℝ) + 2) / f (2 * (i : ℝ) + 1) = 2 := by
      intro i
      specialize h3 i
      simpa using h3
    simp_rw [h6]
    simp [Finset.sum_const, Finset.card_range]
    <;> norm_num
  rw [h5]
  all_goals norm_num