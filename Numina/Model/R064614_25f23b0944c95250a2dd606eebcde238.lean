import Mathlib

theorem algebra_145405 {a : ℕ → ℤ} (ha : a 0 = -1) (ha1 : a 1 = -3) (ha2 : a 2 = -5)
    (ha3 : a 3 = 5) (h : ∀ n ≥ 4, a n = 8 * a (n - 1) - 22 * a (n - 2) + 24 * a (n - 3) - 9 * a (n - 4)) :
    ∀ n, a n = 2 + n - 3 ^ (n + 1) + n * 3 ^ n := by
  intro n
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero =>
    simp [ha]
    <;> ring
  | succ n =>
    cases n with
    | zero =>
      simp [ha1]
      <;> ring
    | succ n =>
      cases n with
      | zero =>
        simp [ha2]
        <;> ring
      | succ n =>
        cases n with
        | zero =>
          simp [ha3]
          <;> ring
        | succ n =>
          have eq1 := ih (n + 3) (by linarith)
          have eq2 := ih (n + 2) (by linarith)
          have eq3 := ih (n + 1) (by linarith)
          have eq4 := ih (n) (by linarith)
          specialize h (n + 4) (by omega)
          simp [h, eq1, eq2, eq3, eq4]
          all_goals
            ring_nf
            <;> omega