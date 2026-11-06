import Mathlib

theorem algebra_301768 {a : ℕ → ℤ} (ha1 : a 1 = 1)
    (han : ∀ n > 0, a (n + 1) = 2 * a n - n + 2) :
    ∀ n, ∑ i in Finset.Icc 1 n, a i = 2 ^ n - 1 + n * (n - 1) / 2 := by
  intro n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h2 : ∀ (n : ℕ), a (n + 1) = 2 ^ n + n := by
      intro n
      induction n with
      | zero =>
        simp [ha1]
      | succ n ih =>
        have eq1 : a (n + 2) = 2 * a (n + 1) - (n + 1) + 2 := by
          specialize han (n + 1) (by linarith)
          simpa using han
        rw [eq1]
        rw [ih]
        simp [pow_succ, mul_add, mul_sub]
        <;> ring_nf
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [ih]
    have eq2 : a (n + 1) = 2 ^ n + n := h2 n
    simp [eq2]
    <;> ring_nf
    <;> omega