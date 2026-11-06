import Mathlib

theorem number_theory_176402 (n : ℕ) (h₀ : n > 0) :
    ¬ Nat.Prime (∑ i ∈ Finset.range 1000, (n + i)) := by
  have h1 : ∑ i in Finset.range 1000, (n + i) = 1000 * n + 499500 := by 
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [show ∑ i in Finset.range 1000, i = (499500 : ℕ) by native_decide]
    all_goals ring
  rw [h1]
  have h2 : (1000 * n + 499500 : ℕ) = 100 * (10 * n + 4995) := by 
    omega
  rw [h2]
  apply Nat.not_prime_mul (by norm_num) (by
    omega
  )