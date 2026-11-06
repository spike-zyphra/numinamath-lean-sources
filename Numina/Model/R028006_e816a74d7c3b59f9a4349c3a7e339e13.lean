import Mathlib

theorem algebra_213202 (a : ℕ → ℝ) (ha1 : a 1 = 1) (han : ∀ n ≥ 1, a (n + 1) = (1 / 3) * a n + 1) :
    ∀ n ≥ 1, a n = 3 / 2 - (1 / 2) * (1 / 3) ^ (n - 1) := by
  intro n hn
  induction n with
  | zero =>
    exfalso
    exact Nat.lt_irrefl 0 hn
  | succ n ih =>
    cases n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n =>
      have h1 := ih (by linarith)
      have h2 : a (n + 2) = (1 / 3) * a (n + 1) + 1 := by
        specialize han (n + 1) (by linarith)
        simpa using han
      rw [show n + 1 + 1 = n + 2 by omega]
      rw [h2]
      rw [h1]
      field_simp at *
      ring_nf
      <;> norm_num