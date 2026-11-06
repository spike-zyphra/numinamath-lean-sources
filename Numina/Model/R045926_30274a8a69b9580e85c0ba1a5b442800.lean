import Mathlib

theorem algebra_109336 {a : ℕ → ℤ}
    (ha : ∀ n, a (n + 2) = 5 * a (n + 1) - 6 * a n + 4 ^ (n + 1))
    (ha0 : a 0 = 1) (ha1 : a 1 = 3) :
    ∀ n, a n = 2 ^ (n + 1) - 3 ^ (n + 1) + 2 * 4 ^ n := by
  intro n
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero =>
    simp [ha0]
    <;> norm_num
    all_goals linarith
  | succ n =>
    cases n with
    | zero =>
      simp [ha1]
      <;> norm_num
      all_goals linarith
    | succ n =>
      have h2 := ha n
      have h1 := ih (n + 1) (by omega)
      have h0 := ih (n) (by omega)
      simp [h2, h1, h0] at *
      ring_nf
      <;> norm_num
      all_goals omega