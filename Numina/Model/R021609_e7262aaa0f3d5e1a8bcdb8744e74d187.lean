import Mathlib

theorem algebra_188809 {U : ℕ → ℤ} (hU1 : U 1 = 1) (hU : ∀ k ≥ 1, U (k + 1) = U k + (k + 1)) :
    ∀ n ≥ 1, U n + U (n + 1) = (n + 1)^2 := by
  intro n hn
  have h1 : ∀ n ≥ 1, U n + U (n + 1) = (n + 1)^2 := by
    intro n hn
    induction n with
    | zero => 
      exfalso 
      linarith
    | succ n ih => 
      cases n with 
      | zero => 
        have h11 : U 1 + U (1 + 1) = (1 + 1)^2 := by
          have hU2 : U (1 + 1) = U 1 + (1 + 1) := hU 1 (by norm_num)
          rw [hU2, hU1] 
          all_goals norm_num 
        simpa using h11 
      | succ n => 
        have eq1 : U (n + 1 + 1) = U (n + 1) + (n + 1 + 1 : ℤ) := by
          specialize hU (n + 1) (by linarith)
          simpa using hU 
        have eq2 : U ((n + 1 + 1) + 1) = U (n + 1 + 1) + ((n + 1 + 1 + 1 : ℤ)) := by
          specialize hU (n + 1 + 1) (by linarith)
          simpa using hU 
        have eq3 : U (n + 1) + U (n + 1 + 1) = (n + 1 + 1 : ℤ) ^ 2 := by 
          simpa using ih (by linarith) 
        simp [eq1, eq2] at * 
        all_goals 
          nlinarith [eq1, eq2, eq3, hU (n + 1 + 1) (by linarith), hU (n + 1) (by linarith) ]
  specialize h1 n hn 
  simpa using h1