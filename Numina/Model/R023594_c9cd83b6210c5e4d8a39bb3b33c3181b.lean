import Mathlib

theorem algebra_136872 {f : ℤ → ℤ} (h : ∀ x, f (x + 1) - f x = x + 1) (hf : f 0 = 4) :
    f 62 = 1957 := by
  have eq1 : ∀ n : ℕ, f (n : ℤ) = 4 + n * (n + 1) / 2 := by
    intro n
    induction n with
    | zero =>
      simp [hf]
    | succ k ih =>
      have eq2 : f ((k + 1 : ℕ) : ℤ) = f ((k : ℕ) : ℤ) + (k : ℤ) + 1 := by
        specialize h ((k : ℕ) : ℤ)
        simp at h ⊢
        linarith
      rw [eq2, ih]
      simp [add_assoc, add_comm, add_left_comm, mul_add, add_mul]
      <;> ring_nf <;> omega
  have eq62 : f (62 : ℤ) = 1957 := by
    have eq62 : f (62 : ℤ) = 4 + (62 * (62 + 1) / 2) := by
      specialize eq1 62
      norm_num at eq1 ⊢
      all_goals linarith
    norm_num at eq62 ⊢
    all_goals linarith
  exact eq62