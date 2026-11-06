import Mathlib

theorem algebra_310824 {a : ℕ → ℤ} (ha1 : a 1 = 1) (han : ∀ n ≥ 1, a (n + 1) = 2 * a n + n * (1 + 2 ^ n)) :
    ∀ n ≥ 2, a n = 2 ^ (n - 2) * (n ^ 2 - n + 6) - n - 1 := by 
  intro n hn
  induction n with
  | zero => 
    linarith -- contradiction
  | succ n ih =>
    cases n with
    | zero => 
      linarith -- contradiction
    | succ n => 
      cases n with
      | zero => 
        -- n = 2
        norm_num [ha1, han] -- base case
      | succ n => 
        -- induction step
        have ih' := ih (by linarith)
        simp [han (n + 2) (by linarith)] at ih ⊢
        cases n with
        | zero => 
          norm_num [ha1] at ih ⊢
          <;> omega
        | succ n => 
          simp [pow_succ, pow_mul, mul_add, mul_sub] at ih ⊢
          <;> ring_nf at ih ⊢
          <;> omega