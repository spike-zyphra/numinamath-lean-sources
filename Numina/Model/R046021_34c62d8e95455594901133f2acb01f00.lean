import Mathlib

theorem algebra_197806 {f : ℝ → ℝ} (h0 : f 0 = 1) (hf : ∀ x, f (x + 4) = f x + 3 * x + 4) :
    f 2000 = 1499001 := by
  have h1 : ∀ (n : ℕ), f ((4 * (n : ℝ))) = 6 * ((n : ℝ) )^2 - 2 * ((n : ℝ) ) + 1 := by
    intro n
    induction n with
    | zero =>
      norm_num
      all_goals linarith [h0]
    | succ n ih =>
      have eq2 : f (4 * ((n + 1 : ℕ) : ℝ)) = f (4 * ((n : ℝ) ) + 4) := by
        simp [mul_add, mul_comm]
        <;> ring_nf
        <;> norm_num
      have eq3 : f (4 * ((n : ℝ) ) + 4) = f (4 * ((n : ℝ) ) ) + 3 * (4 * ((n : ℝ) ) ) + 4 := by
        specialize hf (4 * ((n : ℝ) ) )
        have eq4 : (4 * ((n : ℝ) ) ) + 4 = (4 * ((n : ℝ) ) ) + 4 := by ring
        rw [eq4] at hf
        linarith [hf]
      rw [eq2, eq3, ih]
      simp [add_assoc]
      ring_nf
  specialize h1 500
  norm_num at h1 ⊢
  linarith [h1]