import Mathlib

theorem algebra_90047 {f : ℝ → ℝ} (h : ∀ x y, f (x * y) = f x * y + x * f y)
    (x y : ℝ) (hy : y ≠ 0) : f (x / y) = (f x * y - x * f y) / y ^ 2 := by 
  have eq1 : f x = f (x / y) * y + (x / y) * f y := by 
    have h1 : f ((x / y) * y) = f (x / y) * y + (x / y) * f y := h (x / y) y
    have h2 : (x / y) * y = x := by 
      field_simp [hy]
    rw [h2] at h1 
    linarith 
  have eq2 : f (x / y) * y = f x - (x / y) * f y := by linarith [eq1]
  -- Now we need to express f(x / y) * y ^ 2 = f(x) * y - x * f y.
  have eq3 : f (x / y) = (f x * y - x * f y) / y ^ 2 := by 
    have eq4 : f (x / y) * y ^ 2 = f x * y - x * f y := by 
      have eq5 : f (x / y) * (y ^ 2) = f x * y - x * f y := by
        have eq6 : f (x / y) * (y ^ 2) = (f (x / y) * y) * y := by ring
        rw [eq6]
        rw [eq2]
        <;> field_simp [hy] at *
        <;> ring_nf 
      linarith [eq5]
    have h6 : y ^ 2 ≠ 0 := by 
      apply pow_ne_zero 2 
      exact hy 
    field_simp [h6] at eq4 ⊢ 
    <;> linarith [eq4, h6]
  exact eq3