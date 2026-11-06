import Mathlib

theorem algebra_254183 (a : ℕ → ℤ) (ha : ∀ n, a n = a (n + 1) - 3) (ha0 : a 0 = 1) :
    a 999 = 2998 := by
  have h : ∀ n, a n = 1 + 3 * n := by
    intro n
    induction n with
    | zero =>
      -- for n = 0, we know a 0 = 1
      simp [ha0]
    | succ n ih =>
      -- for induction step, we have assumed a n = 1 + 3 * n, need to prove a (n + 1) = 1 + 3 * (n + 1)
      have h1 : a (n + 1) = a n + 3 := by
        specialize ha n
        linarith
      rw [h1]
      rw [ih]
      simp [add_mul, mul_add]
      <;> ring
  have h999 : a 999 = 1 + 3 * 999 := h 999
  norm_num at h999 ⊢
  exact h999