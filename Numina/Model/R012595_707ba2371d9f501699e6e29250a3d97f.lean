import Mathlib

theorem algebra_279009 {f : ℝ → ℝ} (l : ℝ) (hl : l ≠ 0) (h : ∀ x, f (x + l) = f x) :
    ∀ n : ℕ, n ≠ 0 → ∀ x, f (x + n * l) = f x := by 
  intro n hn x
  have h1 : ∀ (n : ℕ), f (x + n * l) = f x := by 
    intro n
    induction n with 
    | zero =>
      simp
    | succ k ih =>
      have eq1 : f (x + (k + 1 : ℕ) * l) = f (x + k * l + l) := by 
        simp [mul_add]
        <;> ring_nf
      have eq2 : f (x + k * l + l) = f (x + k * l) := by 
        specialize h (x + (k * l))
        ring_nf at h ⊢
        all_goals linarith
      rw [eq1, eq2, ih]
  specialize h1 n
  simpa using h1