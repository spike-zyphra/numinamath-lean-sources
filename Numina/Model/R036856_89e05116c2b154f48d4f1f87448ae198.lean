import Mathlib

theorem number_theory_222631 (p : ℕ) (hp : p > 0) : 84 ∣ (4^(2*p) - 3^(2*p) - 7 : ℤ) := by 
  have h1 : ∀ p : ℕ, p > 0 → 84 ∣ (4 ^ (2 * p) - 3 ^ (2 * p) - 7 : ℤ) := by 
    intro p hp
    induction p with 
    | zero => 
      exfalso
      linarith
    | succ p ih =>
      cases p with
      | zero => 
        norm_num at *
      | succ p => 
        simp [pow_add, pow_mul] at ih ⊢ 
        all_goals ring_nf at ih ⊢ 
        all_goals omega 
  specialize h1 p hp 
  simpa using h1