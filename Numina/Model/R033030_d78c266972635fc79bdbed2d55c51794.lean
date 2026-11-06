import Mathlib

open Nat

theorem algebra_5080 {u : ℕ → ℝ} (hu0 : u 0 = 1) (hu1 : u 1 = 1)
    (hun : ∀ n > 0, n * (n + 1) * u (n + 1) + (n - 2) * u (n - 1) = n * (n - 1) * u n) :
    ∀ n, u n = 1 / (n !) := by 
  intro n
  have h4 : ∀ n : ℕ, u n = 1 / (n !) := by
    intro n 
    induction' n using Nat.strongRecOn with n ih
    cases n with 
    | zero =>
      rw [hu0]
      norm_num
    | succ n =>
      cases n with
      | zero =>
        rw [hu1]
        norm_num
      | succ n =>
        have eq1 := hun (n + 1) (by linarith)
        have eq2 : (↑n + 1 : ℝ) * (↑n + 2 : ℝ) * u (n + 1 + 1) + (↑n + 1 - 2 : ℝ) * u (n + 1 - 1) = (↑n + 1 : ℝ) * (↑n : ℝ) * u (n + 1) := by 
          have h1 := eq1 
          simp [show n + 1 + 1 = n + 2 by omega, show n + 1 - 1 = n by omega] at h1 ⊢ 
          linarith
        have eq3 : u n = 1 / (n ! : ℝ) := by 
          specialize ih n (by omega)
          simpa using ih 
        have eq4 : u (n + 1) = 1 / ((n + 1 : ℕ) ! : ℝ) := by 
          specialize ih (n + 1) (by omega)
          simpa using ih 
        have eq5 : u (n + 1 + 1) = 1 / ((n + 1 + 1 : ℕ) ! : ℝ) := by 
          have eq6 : (↑n + 1 : ℝ) * (↑n + 2 : ℝ) * u (n + 1 + 1) = (↑n + 1 : ℝ) * (↑n : ℝ) * u (n + 1) - (↑n + 1 - 2 : ℝ) * u (n + 1 - 1) := by 
            linarith [eq2] 
          have eq7 : (↑n + 1 : ℝ) * (↑n : ℝ) * u (n + 1) = (↑n + 1 : ℝ) * (↑n : ℝ) * (1 / (↑(n + 1) !) ) := by 
            rw [eq4] 
          have eq8 : (↑n + 1 - 2 : ℝ) * u (n + 1 - 1) = (↑n + 1 - 2 : ℝ) * (1 / (↑n !) ) := by 
            have eq9 : u (n + 1 - 1) = 1 / (↑n !) := by 
              have eq10 : n + 1 - 1 = n := by omega 
              rw [eq10] 
              exact_mod_cast eq3 
            rw [eq9] 
          rw [eq7, eq8] at eq6 
          have eq9 : u (n + 1 + 1) = ( ( (↑n + 1 : ℝ) * (↑n : ℝ) * (1 / (↑(n + 1) !) ) - (↑n + 1 - 2 : ℝ) * (1 / (↑n !) ) ) / ( (↑n + 1 : ℝ) * (↑n + 2 : ℝ) ) ) := by 
            have h2 : (↑n + 1 : ℝ) * (↑n + 2 : ℝ) ≠ 0 := by 
              have hn1 : (↑n + 1 : ℝ) ≠ 0 := by positivity 
              have hn2 : (↑n + 2 : ℝ) ≠ 0 := by positivity 
              exact mul_ne_zero hn1 hn2 
            have h1 : (↑n + 1 : ℝ) * (↑n + 2 : ℝ) * u (n + 1 + 1) = ( (↑n + 1 : ℝ) * (↑n : ℝ) * (1 / (↑(n + 1) !) ) - (↑n + 1 - 2 : ℝ) * (1 / (↑n !) ) ) := by linarith [eq6]
            field_simp [h2] at h1 ⊢
            linarith 
          rw [eq9] 
          field_simp [Nat.factorial] at *
          <;> ring_nf 
          <;> 
            try { 
              cases n with 
              | zero => 
                norm_num 
              | succ n => 
                norm_num [Nat.factorial] at *
                <;> ring_nf 
                <;> 
                  try { 
                    nlinarith 
                  } 
            }
        exact_mod_cast eq5 
  specialize h4 n 
  simpa using h4