import Mathlib

theorem number_theory_91182 (n : ℕ) (hn : n > 0) :
    14 ∣ 3 ^ (4 * n + 2) + 5 ^ (2 * n + 1) := by 
  have h1 : ∀ (n : ℕ), n > 0 → 14 ∣ 3 ^ (4 * n + 2) + 5 ^ (2 * n + 1) := by 
    intro n hn 
    induction n with 
    | zero => 
      exfalso 
      linarith 
    | succ n ih =>
      cases n with 
      | zero => 
        norm_num at ih ⊢ 
      | succ n => 
        simp [pow_succ, pow_mul] at ih ⊢ 
        ring_nf at ih ⊢ 
        omega 
  exact h1 n hn