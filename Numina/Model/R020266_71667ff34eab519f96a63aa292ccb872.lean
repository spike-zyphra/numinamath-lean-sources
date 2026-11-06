import Mathlib

def a : ℕ → ℤ
| 0 => 1
| 1 => 4
| 2 => 9
| n + 3 => a (n + 2) + a (n + 1) - a n

theorem algebra_326227 : a 2010 = 8041 := by
  have h1 : ∀ (n : ℕ), a n = 4 * (n : ℤ) + ((-1 : ℤ) ^ n + 1) / 2 := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      simp [a]
    | succ n =>
      cases n with
      | zero =>
        simp [a]
      | succ n =>
        cases n with
        | zero =>
          simp [a]
        | succ n =>
          have h1 := ih n (by linarith)
          have h2 := ih (n + 1) (by linarith)
          have h3 := ih (n + 2) (by linarith)
          simp [a, h1, h2, h3]
          all_goals
            ring_nf
            <;> omega
  have h2 : a 2010 = 4 * (2010 : ℤ) + ((-1 : ℤ) ^ 2010 + 1) / 2 := h1 2010
  rw [h2]
  norm_num