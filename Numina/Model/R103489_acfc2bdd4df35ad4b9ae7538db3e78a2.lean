import Mathlib

theorem number_theory_195927 (n : ℕ) (hn : Odd n) :
    1965 ∣ 73^n + 1049 * 58^n := by 
  have h : Odd n := hn
  rcases h with ⟨k, hk⟩ 
  rw [show n = 2 * k + 1 by omega]
  have h1 : ∀ k : ℕ, 1965 ∣ 73 ^ (2 * k + 1) + 1049 * 58 ^ (2 * k + 1) := by 
    intro k 
    induction k with
    | zero =>
      norm_num
    | succ k ih =>
      norm_num [pow_succ, pow_mul, pow_add] at ih ⊢
      <;> omega 
  specialize h1 k 
  simpa using h1
  all_goals omega