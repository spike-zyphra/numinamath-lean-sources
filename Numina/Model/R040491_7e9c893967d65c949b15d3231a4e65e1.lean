import Mathlib

def f (n : ℕ) := ∑ i ∈ Finset.range n, (10 ^ (i + 1) - 1) / 9

theorem number_theory_283992 (n : ℕ) :
    f n = (10 ^ (n + 1) - 10 - 9 * n) / 81 := by 
  have h1 : ∀ (n : ℕ), f n = (10 ^ (n + 1) - 10 - 9 * n) / 81 := by
    intro n
    induction n with 
    | zero =>
      simp [f]
    | succ n ih =>
      have eq1 : f (n + 1) = f n + (10 ^ (n + 1) - 1) / 9 := by 
        simp [f, Finset.sum_range_succ]
      rw [eq1, ih]
      have h_eq : (10 ^ (n + 1) - 10 - 9 * n) / 81 + (10 ^ (n + 1) - 1) / 9 = (10 ^ (n + 1 + 1) - 10 - 9 * (n + 1)) / 81 := by
        have h1 : ∀ k : ℕ, (10 ^ (k + 1) - 10 - 9 * k) + (81 * ((10 ^ (k + 1) - 1) / 9)) = (10 ^ (k + 1 + 1) - 10 - 9 * (k + 1)) := by
          intro k
          induction k with 
          | zero =>
            norm_num
          | succ k ih2 =>
            simp [pow_succ, pow_zero, Nat.add_assoc, Nat.mul_add, Nat.add_mul, mul_assoc] at ih2 ⊢
            all_goals 
              try norm_num at ih2 ⊢
              <;> omega 
        have h2 := h1 n 
        omega 
      exact h_eq 
  specialize h1 n 
  simpa using h1