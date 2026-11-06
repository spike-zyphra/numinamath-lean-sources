import Mathlib

theorem algebra_198331 {a : ℕ → ℤ} (ha : ∀ n, a (n + 2) = 4 * a (n + 1) - 3 * a n + 2 ^ (n + 2))
    (ha0 : a 0 = 2) (ha1 : a 1 = 8) :
    ∀ n, a n = 1 + 5 * 3 ^ n - 4 * 2 ^ n := by
  intro n
  induction' n using Nat.strongRec with n ih
  cases n with
  | zero =>
    simp [ha0]
    all_goals norm_num [ha0]
  | succ n =>
    cases n with
    | zero =>
      simp [ha1]
      all_goals norm_num [ha1]
    | succ n =>
      have eq1 := ih (n + 1) (by omega)
      have eq2 := ih n (by omega)
      have eq3 := ha n
      simp [eq1, eq2, eq3]
      ring_nf
      all_goals omega
      all_goals try { tauto }
      all_goals try { omega }
      all_goals try { ring }