import Mathlib

theorem number_theory_174374 (k : ℕ) :
    7 ∣ 2^(6*k + 1) + 3^(6*k + 1) + 5^(6*k) + 1 := by
  have h1 : ∀ k : ℕ, 7 ∣ 2^(6*k + 1) + 3^(6*k + 1) + 5^(6*k) + 1 := by
    intro k
    induction k with
    | zero =>
      norm_num
    | succ k ih =>
      norm_num [Nat.pow_succ, Nat.pow_mul] at ih ⊢
      <;> ring_nf at ih ⊢ 
      <;> omega
  specialize h1 k
  simpa using h1