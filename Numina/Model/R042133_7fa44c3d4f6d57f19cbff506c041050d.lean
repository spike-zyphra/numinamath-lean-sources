import Mathlib

theorem number_theory_105924 (x : ℕ) (hx : x > 0) (h : Nat.Prime (x^5 + x + 1)) :
    x = 1 := by 
  by_cases hx1 : x > 1 
  · -- Assume x > 1. Then x ≥ 2.
    have h1 : x ≥ 2 := by omega 
    have h2 : x ^ 5 + x + 1 = (x^2 + x + 1) * (x^3 - x^2 + 1) := by
      cases x with 
      | zero => linarith 
      | succ x => 
        cases x with 
        | zero => linarith 
        | succ x => 
          simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
          <;> ring_nf <;> omega 
    rw [h2] at h 
    have h3 : x ^ 2 + x + 1 > 1 := by 
      nlinarith [h1, sq_nonneg (x : ℕ)]
    have h4 : x^3 - x^2 + 1 > 1 := by 
      have h5 : x ≥ 2 := h1 
      have h6 : x ^ 3 ≥ x ^ 2 + 4 := by 
        nlinarith [sq_nonneg ((x : ℕ) - 1), sq_nonneg ((x : ℕ)), h5, sq_nonneg (x * (x - 1))]
      have h7 : x ^ 3 - x ^ 2 ≥ 4 := by 
        have h8 : x ^ 3 ≥ x ^ 2 + 4 := h6 
        omega 
      omega 
    exfalso 
    have h10 : ¬ Nat.Prime ((x^2 + x + 1) * (x^3 - x^2 + 1)) := by 
      apply Nat.not_prime_mul 
      all_goals 
        omega 
    tauto 
  · -- Assume $\neg (x > 1)$. Then $x \le 1$. Combined with $x > 0$, this gives $x = 1$.
    have h3 : x ≤ 1 := by 
      omega 
    have h4 : x = 1 := by 
      omega 
    exact h4