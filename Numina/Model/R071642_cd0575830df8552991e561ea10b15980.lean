import Mathlib

theorem algebra_311233 {a : ℕ → ℤ} (ha1 : a 1 = 2)
    (han : ∀ n ≥ 2, a n = 2^(2*n) * a (n - 1) + 2^(n^2) * n) :
    ∀ n ≥ 1, a n = 2^(n^2) * (2^(n + 1) - n - 2) := by
  intro n hn
  induction n with
  | zero =>
    exfalso
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n =>
      have ih' := ih (by linarith)
      have h1 : a (n + 1 + 1) = 2 ^ (2 * (n + 1 + 1)) * a (n + 1) + 2 ^ ((n + 1 + 1) ^ 2) * (n + 1 + 1) := by
        specialize han (n + 1 + 1) (by linarith)
        simpa using han
      simp [h1, ih']
      ring_nf
      <;> simp [pow_succ, pow_mul, mul_add, mul_assoc]
      <;> ring_nf
      <;> omega