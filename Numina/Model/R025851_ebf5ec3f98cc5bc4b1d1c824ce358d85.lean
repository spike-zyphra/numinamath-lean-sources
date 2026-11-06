import Mathlib

theorem algebra_309364 (a : ℕ → ℝ) (h₀ : ∃ d, ∀ n, a n = a 0 + d * n)
    (h₁ : ∑ i in Finset.range m, a i = 90) (h₂ : ∑ i in Finset.range (2 * m), a i = 360) :
    ∑ i in Finset.range (4 * m), a i = 1440 := by
  rcases h₀ with ⟨d, hd⟩
  have h3 : ∀ (n : ℕ), ∑ i in Finset.range n, a i = (n : ℝ) / 2 * (2 * a 0 + (n - 1) * d) := by 
    intro n
    have h4 : ∀ (k : ℕ), ∑ i in Finset.range k, a i = (k : ℝ) / 2 * (2 * a 0 + (k - 1) * d) := by
      intro k
      induction k with
      | zero => 
        simp 
        <;> ring_nf <;> norm_num
      | succ k ih => 
        rw [Finset.sum_range_succ, ih]
        simp [add_mul, mul_add, hd k] at *
        <;> ring_nf <;> field_simp at *
        <;> ring_nf <;> linarith 
    specialize h4 n 
    simpa using h4
  have eq1 := h3 m 
  have eq2 := h3 (2 * m)
  have eq3 := h3 (4 * m)
  norm_num at eq1 eq2 eq3
  rw [eq1] at h₁
  rw [eq2] at h₂
  rw [eq3]
  nlinarith [ sq_nonneg (m : ℝ), sq_nonneg (a 0), sq_nonneg (d), sq_nonneg ((a 0 : ℝ) - (d : ℝ)), sq_nonneg (( (m : ℝ) - 1 : ℝ) * (d : ℝ)), sq_nonneg (( (m : ℝ) * (d : ℝ)) ) ]