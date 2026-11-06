import Mathlib

theorem algebra_197309 {f : ℤ → ℤ} (hf0 : f 0 = 1) (hfx : ∀ x, f (x + 2) = f x + 3 * x + 2) :
    f 3000 = 6748501 := by
  have h1 : ∀ (n : ℕ), f (2 * (n : ℤ)) = 3 * (n : ℤ) ^ 2 - (n : ℤ) + 1 := by
    intro n
    induction n with
    | zero =>
      norm_num
      <;> linarith [hf0]
    | succ n ih =>
      have eq1 : f (2 * ((n + 1 : ℕ) : ℤ)) = f (2 * ((n : ℕ) : ℤ) + 2) := by
        simp [show (n + 1 : ℕ) = n + 1 by rfl]
        <;> ring_nf <;> norm_num
        <;> tauto
      rw [eq1]
      have eq2 : f (2 * ((n : ℕ) : ℤ) + 2) = f (2 * ((n : ℕ) : ℤ)) + 3 * (2 * ((n : ℕ) : ℤ)) + 2 := by
        apply hfx
      rw [eq2, ih]
      simp [add_mul, mul_add, pow_two]
      <;> ring_nf
  have h2 : f 3000 = 3 * (1500 : ℤ) ^ 2 - (1500 : ℤ) + 1 := by
    have h3 := h1 1500
    norm_num at h3 ⊢
    <;> linarith
  rw [h2]
  all_goals
    norm_num