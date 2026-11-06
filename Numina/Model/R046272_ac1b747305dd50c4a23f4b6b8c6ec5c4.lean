import Mathlib

/- \( k \)-th Fermat number -/
abbrev F_4603 (k : ℕ) := 2 ^ (2 ^ k) + 1

theorem number_theory_4603 :
    ∀ n : ℕ, n > 0 → ∏ i ∈ Finset.range n, F_4603 i = F_4603 n - 2 := by
  intro n hn 
  induction n with 
  | zero =>
    exfalso 
    exact Nat.lt_irrefl 0 hn 
  | succ n ih =>
    cases n with 
    | zero =>
      simp [F_4603] at *
    | succ n => 
      rw [Finset.prod_range_succ, ih (by linarith)]
      rw [show F_4603 (n + 1) = 2 ^ (2 ^ (n + 1)) + 1 by rfl] 
      rw [show F_4603 (n + 1 + 1) = 2 ^ (2 ^ (n + 1 + 1)) + 1 by rfl] 
      have eq1 : ((2 ^ (2 ^ (n + 1)) + 1 - 2) : ℕ) * ((2 ^ (2 ^ (n + 1)) + 1 ) : ℕ ) = ((2 ^ (2 ^ (n + 1 + 1))) + 1 - 2 ) := by
        have eq2 : (2 ^ (2 ^ (n + 1 + 1)) ) = (2 ^ (2 ^ (n + 1)) ) ^ 2 := by 
          ring_nf 
        calc 
          ((2 ^ (2 ^ (n + 1)) + 1 - 2 ) : ℕ) * ((2 ^ (2 ^ (n + 1)) + 1 ) : ℕ ) 
            = ((2 ^ (2 ^ (n + 1)) - 1 ) : ℕ ) * ((2 ^ (2 ^ (n + 1)) + 1 ) : ℕ ) := by 
              cases (2 ^ (2 ^ (n + 1)) ) with 
              | zero => 
                all_goals omega 
              | succ m => 
                simp [Nat.add_sub_cancel] 
          _ = ((2 ^ (2 ^ (n + 1)) ) ^ 2 - 1 ) := by 
            cases (2 ^ (2 ^ (n + 1)) ) with 
            | zero => 
              all_goals omega 
            | succ m => 
              simp [Nat.mul_sub, Nat.sub_mul, Nat.add_sub_cancel, mul_add] 
              <;> ring_nf 
              <;> omega 
          _ = ( (2 ^ (2 ^ (n + 1 + 1)) ) - 1 ) := by 
            rw [eq2] 
          _ = ( (2 ^ (2 ^ (n + 1 + 1)) ) + 1 - 2 ) := by 
            omega 
      simpa using eq1