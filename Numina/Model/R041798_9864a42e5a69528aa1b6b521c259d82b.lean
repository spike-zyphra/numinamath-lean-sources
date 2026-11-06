import Mathlib

theorem algebra_148924 {a : ℕ → ℝ}
    (ha1 : a 1 = Real.sqrt 2 / 2 + 1)
    (ha2 : a 2 = Real.sqrt 2 + 1)
    (han : ∀ n ≥ 2, a (n + 1) + a (n - 1) = (n / (a n - a (n - 1))) + 2) :
    ∀ n ≥ 1, a n = n * Real.sqrt 2 / 2 + 1 := by 
  intro n hn 
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero => linarith
  | succ n => 
    cases n with
    | zero => norm_num [ha1]
    | succ n => 
      cases n with
      | zero => norm_num [ha2]
      | succ n => 
        have eq1 := ih (n+1) (by omega) (by omega)
        have eq2 := ih (n+2) (by omega) (by omega)
        have h3 := han (n+2) (by omega)
        simp [show n + 2 + 1 = n + 3 by omega, show n + 2 - 1 = n + 1 by omega] at h3
        simp [eq1, eq2] at h3 ⊢
        ring_nf at h3 ⊢
        field_simp [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          mul_add, add_mul] at h3 ⊢
        <;> ring_nf at h3 ⊢
        <;> norm_num [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)] at h3 ⊢
        <;> nlinarith [mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), 
            mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), 
            Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
            Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
            sq_nonneg (Real.sqrt 2), sq_nonneg (Real.sqrt 2 - 2)]