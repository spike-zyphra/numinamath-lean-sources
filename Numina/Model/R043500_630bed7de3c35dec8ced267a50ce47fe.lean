import Mathlib

open Finset

theorem other_40557 {T : ℕ → ℤ} 
  (hT0 : T 0 = 2) (hT1 : T 1 = 3)
  (hT2 : T 2 = 6)
  (hTn : ∀ n ≥ 3, T n = (n + 4) * T (n - 1) - 4 * n * T (n - 2) + (4 * n - 8) * T (n - 3)) :
  ∀ n, T n = n.factorial + 2 ^ n := by 
  intro n 
  induction' n using Nat.strongRecOn with n ih 
  cases n with 
  | zero => 
    rw [hT0]
    simp [Nat.factorial]
  | succ n => 
    cases n with 
    | zero => 
      rw [hT1]
      simp [Nat.factorial]
    | succ n => 
      cases n with 
      | zero => 
        rw [hT2]
        simp [Nat.factorial]
      | succ n => 
        have eq1 := hTn (n + 3) (by linarith)
        have h1 := ih (n) (by linarith)
        have h2 := ih (n + 1) (by linarith)
        have h3 := ih (n + 2) (by linarith)
        simp [show n + 3 - 1 = n + 2 by omega, 
            show n + 3 - 2 = n + 1 by omega, 
            show n + 3 - 3 = n by omega] at eq1 
        simp [Nat.factorial] at h1 h2 h3 eq1 ⊢ 
        ring_nf at eq1 h1 h2 h3 ⊢ 
        rw [eq1]
        <;> try { 
          all_goals 
          try { 
            omega 
          } 
        }
        <;> try { 
          all_goals 
          try { 
            nlinarith 
          } 
        }