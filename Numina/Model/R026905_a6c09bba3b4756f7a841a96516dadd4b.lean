import Mathlib

theorem algebra_277052 (t : ℕ → ℤ) (ht1 : t 1 = 5) (hfn : ∀ n ≥ 2, t n - t (n - 1) = 2 * n + 3) :
    t 50 = 2700 := by

  have h1 : ∀ n : ℕ, t (n + 1) = (n + 1 : ℤ) ^ 2 + 4 * (n + 1 : ℤ) := by
    intro n
    induction n with
    | zero =>
      simp [ht1]
    | succ n ih =>
      have h2 := hfn (n + 2) (by linarith)
      have eq1 : t (n + 2) - t (n + 1) = 2 * (n + 2 : ℤ) + 3 := by
        simpa using h2
      have eq2 : t (n + 2) = t (n + 1) + (2 * (n + 2 : ℤ) + 3) := by
        linarith
      rw [eq2, ih]
      simp [pow_two, mul_add, add_mul]
      <;> ring

  have h50 := h1 49
  norm_num at h50 ⊢
  <;> linarith