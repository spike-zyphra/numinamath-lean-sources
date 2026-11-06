import Mathlib

theorem algebra_197563 {f : ℝ → ℝ} (h₀ : f 0 = 1) (h₁ : ∀ x, f (x + 3) = f x + 2 * x + 3) :
    f 3000 = 3000001 := by
  have h2 : ∀ (n : ℕ), f (3 * (n : ℝ)) = 1 + 3 * ((n : ℝ) )^2 := by
    intro n
    induction n with
    | zero =>
      simp [h₀]
      <;> norm_num
    | succ n ih =>
      have eq1 : f (3 * ((n + 1 : ℕ) : ℝ)) = f (3 * ((n : ℕ) : ℝ) + 3) := by
        simp at *
        <;> ring_nf
        <;> norm_num
      have eq2 : f (3 * ((n : ℕ) : ℝ) + 3) = f (3 * ((n : ℕ) : ℝ)) + 2 * (3 * ((n : ℝ) )) + 3 := by
        specialize h₁ (3 * ((n : ℕ) : ℝ))
        simpa using h₁
      rw [eq1, eq2, ih]
      simp [pow_two]
      <;> ring_nf
      <;> norm_num
  specialize h2 1000
  norm_num at h2 ⊢
  nlinarith