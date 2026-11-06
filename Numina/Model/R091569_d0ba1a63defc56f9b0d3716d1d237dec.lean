import Mathlib

theorem number_theory_1635 (n : ℕ) (hn : 0 < n) :
    8 ∣ 3^(2*n) - 1 := by
  have h1 : ∀ n : ℕ, 0 < n → 8 ∣ 3 ^ (2 * n) - 1 := by
    intro n hn
    induction n with
    | zero =>
      exfalso
      exact Nat.lt_irrefl 0 hn
    | succ n ih =>
      cases n with
      | zero =>
        norm_num
      | succ n =>
        simp [pow_succ, pow_mul] at ih ⊢
        <;> omega
  exact h1 n hn