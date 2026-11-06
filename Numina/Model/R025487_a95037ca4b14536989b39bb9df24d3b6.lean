import Mathlib

theorem number_theory_36069 (n : ℕ) (hn : n > 0) :
    7 ∣ 3^(3*n+1) + 5^(3*n+2) + 7^(3*n+3) := by 
  have h1 : ∀ (n : ℕ), n > 0 → 7 ∣ 3 ^ (3 * n + 1) + 5 ^ (3 * n + 2) + 7 ^ (3 * n + 3) := by
    intro n hn
    induction n with
    | zero =>
      exfalso
      linarith
    | succ n ih =>
      cases n with
      | zero =>
        norm_num at ih ⊢
        all_goals omega
      | succ n =>
        simp [pow_succ, pow_mul] at ih ⊢
        all_goals ring_nf at ih ⊢
        all_goals omega
  specialize h1 n hn
  simpa using h1