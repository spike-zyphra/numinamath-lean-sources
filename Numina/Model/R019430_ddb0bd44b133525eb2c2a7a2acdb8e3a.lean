import Mathlib

theorem algebra_241510 {n : ℕ} (hn : n = 432) :
    ∃ p : Polynomial ℕ, p.degree = 3 ∧ ∀ k ∈ Finset.range 5, p.coeff k < 5 ∧
      p.eval 5 = n := by 
  rw [hn]
  use (Polynomial.C 2 + Polynomial.C 1 * Polynomial.X + Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X ^ 3)
  constructor
  · -- Show that the degree is 3
    compute_degree!
    all_goals norm_num
  · -- Show that for all k in range 5, p.coeff k < 5 ∧ p.eval 5 = 432
    intro k hk
    fin_cases hk <;> simp [Polynomial.coeff_eq_zero_of_natDegree_lt, add_assoc] <;> try native_decide