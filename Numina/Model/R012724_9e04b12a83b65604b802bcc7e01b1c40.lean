import Mathlib

theorem algebra_308114 {a : ℕ → ℝ} (ha1 : a 1 = 1) (ha2 : a 2 = -3 / 2)
    (hak : ∀ k ≥ 1, 4 * a (k + 2) - 12 * a (k + 1) + 9 * a k = 0) :
    ∀ n ≥ 1, a n = (3 - 2 * n) * (3 / 2) ^ (n - 1) := by
  intro n hn
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero => 
    exfalso 
    linarith 
  | succ n => 
    cases n with 
    | zero => 
      rw [ha1]
      norm_num 
    | succ n => 
      cases n with 
      | zero => 
        rw [ha2]
        norm_num 
      | succ k => 
        have eq1 := hak (k + 1) (by linarith)
        have eq2 := ih (k + 2) (by linarith)
        have eq3 := ih (k + 1) (by linarith)
        simp [pow_add, pow_mul, pow_succ, mul_add, mul_sub] at eq2 eq3 eq1 
        have eq4 : a (k + 3) = 3 * a (k + 2) - (9 / 4) * a (k + 1) := by 
          linarith
        have eq5 : a (k + 3) = (3 - 2 * (k + 3)) * (3 / 2) ^ ((k + 3) - 1) := by
          rw [eq4]
          rw [eq2, eq3]
          field_simp [pow_add, pow_mul, pow_succ]
          ring_nf
        exact_mod_cast eq5