import Mathlib

open Nat

theorem inequalities_130414 {n : ℕ} (hn : n > 2) : (n !) * (n !) > n * n := by
  have h1 : n ≥ 3 := by
    omega
  by_cases h4 : n ≤ 6
  · -- n ≤ 6, so n = 3, 4, 5, 6
    interval_cases n <;> try { 
      simp [Nat.factorial] <;> all_goals
      omega 
    }
    <;> norm_num [Nat.factorial]
  · -- n > 6, so n ≥ 7
    have h8 : n ≥ 7 := by
      omega
    have h9 : n ! > n ^ 2 := by 
      have base2 : (7 : Nat) ! > (7 : Nat) ^ 2 := by
        norm_num [Nat.factorial]
      have step2 : ∀ (k : Nat), k ≥ 7 → (k ! > k ^ 2) → ((k + 1) ! > (k + 1) ^ 2) := by 
        intros k hk1 hk2
        have eq1 : (k + 1) ! = (k + 1) * k ! := by 
          simp [Nat.factorial]
          <;> linarith 
        have eq3 : (k + 1) ^ 2 = (k + 1) * (k + 1) := by 
          ring 
        rw [eq1]
        nlinarith [sq_nonneg ((k : Nat) * (k : Nat)), sq_nonneg ((k + 1 : Nat)), 
            mul_pos (show 0 < k by linarith) (show 0 < k + 1 by linarith), 
            sq_nonneg (k * (k : Nat) - (k + 1) * 1 : Nat), 
            pow_pos (show 0 < k by linarith) 2, 
            pow_pos (show 0 < k + 1 by linarith) 2, 
            hk2
            ]
      exact Nat.le_induction base2 step2 n (by omega)
    have eq7 : n ! * n ! > n * n := by
      nlinarith [h9, sq_nonneg (n : Nat), sq_nonneg (n ! : Nat), 
          sq_pos_of_pos (show 0 < n by omega), 
          mul_pos (show 0 < n by omega) (show 0 < n by omega)
      ]
    linarith