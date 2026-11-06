import Mathlib

theorem algebra_194259 {a : ℕ → ℝ} (ha1 : a 1 = 1)
    (han : ∀ n > 0, a (n + 1) = ((n ^ 2 + n) * a n) / (3 * a n + n ^ 2 + n)) :
    ∀ n > 0, a n = n / (4 * n - 3) := by
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
      have ih' : a (n + 1) = (↑n + 1) / (4 * (↑n + 1) - 3) := by
        simpa using ih (by linarith)
      have h1 : a (n + 1 + 1) = ((n + 1: ℝ) ^ 2 + (n + 1 : ℝ)) * a (n + 1) / (3 * a (n + 1) + (n + 1: ℝ) ^ 2 + (n + 1 : ℝ)) := by
        specialize han (n + 1) (by linarith)
        simpa using han
      rw [h1]
      rw [ih']
      field_simp [(show (4 * ((↑n + 1) : ℝ) - 3 : ℝ) ≠ 0 by
        have h1 : (↑n + 1 : ℝ) ≥ 1 := by
          have hn1 : n + 1 ≥ 1 := by omega
          exact_mod_cast hn1
        nlinarith
      ), (show ((↑n + 1 : ℝ) ) ≠ 0 by
          have h1 : (↑n + 1 : ℝ) ≥ 1 := by
            have hn1 : n + 1 ≥ 1 := by omega
            exact_mod_cast hn1
          linarith
        )
      ]
      <;> ring_nf
      <;> field_simp
      <;> ring_nf <;> linarith