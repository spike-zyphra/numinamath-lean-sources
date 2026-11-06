import Mathlib

theorem algebra_10634 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 - 10 * x + 24) :
    IsLeast {x | ∃ y, f x = y ∧ ∀ x', f x' ≥ y} 5 := by
  constructor
  · -- Show that 5 is in the set
    use -1
    constructor
    · -- Show that f 5 = -1
      rw [hf]
      norm_num
    · -- Show that ∀ x', f x' ≥ -1
      intro x'
      rw [hf]
      simp
      have h : (x' - 5) ^ 2 ≥ 0 := by 
        exact sq_nonneg (x' - 5)
      linarith
  · -- Show that 5 is the least in the set
    intro x hx
    rcases hx with ⟨y, hy1, hy2⟩
    have h1 : f x = y := hy1 
    have h2 : ∀ x', f x' ≥ y := hy2
    have h3 : f 5 ≥ y := h2 5
    have f5 : f 5 = -1 := by 
      rw [hf]
      norm_num 
    have h4 : y ≤ -1 := by 
      linarith [f5, h3]
    have hx_eq2 : x ^ 2 - 10 * x + 24 = y := by 
      rw [hf] at h1 
      simp at h1 ⊢ 
      linarith 
    have h5 : x ^ 2 - 10 * x + 24 ≤ -1 := by 
      linarith [hx_eq2, h4] 
    have h6 : (x - 5) ^ 2 ≤ 0 := by 
      nlinarith 
    have h7 : (x - 5) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (x - 5)]
    have h8 : x - 5 = 0 := by 
      rw [sq_eq_zero_iff] at h7 
      exact h7 
    linarith