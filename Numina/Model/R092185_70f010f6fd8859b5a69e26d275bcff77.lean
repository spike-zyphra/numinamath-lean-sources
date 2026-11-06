import Mathlib

theorem algebra_151489 {a : ℕ → ℤ} (ha1 : a 1 = 2) (han : ∀ n, a (n + 1) = a n + 2 * n) :
    a 100 = 9902 := by

  have eq1 : ∀ (n : ℕ), a (n + 1) = a n + 2 * n := by
    intro n
    apply han

  have h1 : ∀ n, a (n + 1) = 2 + (n + 1) * n := by
    intro n
    induction n with
    | zero =>
      norm_num [ha1]
    | succ n ih =>
      have h2 : a ((n + 1) + 1) = a (n + 1) + 2 * (n + 1) := by
        apply han
      rw [h2]
      rw [ih]
      simp [add_mul, mul_add]
      <;> ring
  have h2 := h1 99
  norm_num at h2 ⊢
  linarith [h2]