import Mathlib


theorem algebra_127245 {a : ℕ → ℤ} (ha1 : a 1 = 2)
    (han : ∀ n ≥ 2, a n = 2 * (n + a (n - 1))) :
    ∀ n ≥ 1, a n = 2 ^ (n + 2) - 2 * n - 4 := by
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
      have h1 : a (n + 2) = 2 * ((n + 2) + a (n + 1)) := by
        specialize han (n + 2) (by linarith)
        simpa using han
      have h2 : a (n + 1) = 2 ^ (n + 1 + 2) - 2 * (n + 1) - 4 := by
        specialize ih (by linarith)
        simpa using ih
      rw [h1, h2]
      simp [pow_add, pow_mul, mul_add]
      <;> ring_nf <;> omega