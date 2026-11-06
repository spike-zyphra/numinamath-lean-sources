import Mathlib

def a : ℕ → ℤ
| 0 => 1
| 1 => 2
| n + 2 => 3 * a (n + 1) - 2 * a n

theorem algebra_219297 : a 2001 = 2 ^ 2001 := by
  have h1 : ∀ n : ℕ, a n = 2 ^ n := by 
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
        have h2 := ih (n) (by omega)
        have h3 := ih (n + 1) (by omega)
        simp [a] at *
        <;> ring_nf at h2 h3 ⊢
        <;> omega
  specialize h1 2001
  simpa using h1