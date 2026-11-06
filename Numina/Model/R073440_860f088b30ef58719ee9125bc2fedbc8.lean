import Mathlib

theorem algebra_197645 {f : ℝ → ℝ} (h0 : f 0 = 1) (hf : ∀ x, f (x + 3) = f x + 2 * x + 3) :
    f 4500 = 6750001 := by

  have h : ∀ n : ℕ, f (3 * (n : ℝ)) = 1 + 3 * ((n : ℝ) ^ 2) := by
    intro n
    induction n with
    | zero =>
      simp [h0]
      <;> ring_nf <;> norm_num
    | succ n ih =>
      have eq1 : f (3 * ((n + 1 : ℕ) : ℝ)) = f (3 * ((n : ℕ) : ℝ) + 3) := by 
        simp [mul_add, add_mul]
        <;> ring_nf <;> simp [Nat.cast_add]
        <;> ring
      rw [eq1]
      have eq2 : f (3 * ((n : ℕ) : ℝ) + 3) = f (3 * ((n : ℕ) : ℝ)) + 2 * (3 * ((n : ℕ) : ℝ)) + 3 := by
        apply hf
      rw [eq2]
      simp [ih]
      <;> ring_nf <;> norm_num
      <;> ring
  have h4500 : f 4500 = 1 + 3 * (1500 : ℝ) ^ 2 := by
    specialize h 1500
    norm_num at h ⊢
    exact h
  rw [h4500]
  norm_num