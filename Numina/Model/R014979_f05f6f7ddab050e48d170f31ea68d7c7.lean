import Mathlib

theorem algebra_251008 {a : ℕ → ℝ} (ha1 : a 1 = 2) (han : ∀ n > 0, (n + 1) * a (n + 1) = a n + n) :
    ∀ n > 0, a n = 1 / Nat.factorial n + 1 := by
  intro n hn
  induction n with
  | zero => 
    exfalso
    linarith
  | succ n ih =>
    cases n with
    | zero => 
      rw [ha1]
      norm_num [Nat.factorial]
    | succ n => 
      have eq1 := ih (by linarith)
      have eq2 := han (n + 1) (by linarith)
      simp [show n + 1 + 1 = n + 2 from by omega] at eq2 ⊢ 
      simp [Nat.factorial] at eq1 eq2 ⊢ 
      <;> field_simp [eq1] at eq2 ⊢ 
      <;> ring_nf at eq1 eq2 ⊢ 
      <;> norm_num [mul_add, add_mul] at eq1 eq2 ⊢ 
      all_goals
        ring_nf at eq1 eq2 ⊢ 
        <;> nlinarith [sq_nonneg (a (n + 2) : ℝ), sq_nonneg (a (n + 1) - 1 : ℝ), sq_nonneg (a (n + 1) * ↑n.factorial : ℝ), sq_nonneg (a (n + 1) * ↑n : ℝ)]