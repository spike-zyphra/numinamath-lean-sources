import Mathlib

theorem algebra_8455 {n : ℕ} (hn : n > 0) (k : ℕ) (hk : k ≥ 2 * n + 1)
    (x : Fin k → ℝ) (hx : StrictMono x) :
    ∃ P Q : Polynomial ℝ, P.degree = n ∧ Q.degree = n ∧
      ∀ i : Fin k, P.eval (x i) ≠ Q.eval (x i) := by

  by_cases h : n = 0 
  · -- Case where n = 0, which contradicts hn : n > 0 
    have hn0 : n = 0 := h 
    exfalso 
    linarith [show n > 0 from hn, show n = 0 by omega]

  · -- Case where n > 0 
    have hn' : n > 0 := by 
      omega 
    use Polynomial.X ^ n + 1 
    use Polynomial.X ^ n 
    constructor 
    · -- Show that the degree of P is n 
      have eq1 : (Polynomial.X ^ n + 1 : Polynomial ℝ) = (Polynomial.X ^ n : Polynomial ℝ) + (1 : Polynomial ℝ) := by ring 
      rw [eq1] 
      have eq2 : (1 : Polynomial ℝ).degree = (0 : WithBot ℕ) := by 
        simp [Polynomial.degree_C] 
      have eq3 : (Polynomial.X ^ n : Polynomial ℝ).degree = (n : WithBot ℕ) := by 
        simp [Polynomial.degree_X_pow] 
      have eq4 : (1 : Polynomial ℝ).degree < (Polynomial.X ^ n : Polynomial ℝ).degree := by 
        rw [eq2, eq3] 
        have h_eq : (n : WithBot ℕ) > (0 : WithBot ℕ) := by 
          have hn_pos' : n > 0 := hn'
          simp [WithBot.coe_lt_coe] at *
          all_goals 
            omega 
        exact h_eq 
      rw [Polynomial.degree_add_eq_left_of_degree_lt eq4]
      rw [eq3] 

    constructor 
    · -- Show that the degree of Q is n 
      have eq41 : (Polynomial.X ^ n : Polynomial ℝ).degree = (n : WithBot ℕ) := by 
        simp [Polynomial.degree_X_pow]
      exact eq41 
    · -- Show that both polynomials evaluate to different values at all points 
      intro i 
      simp [Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_C]
      all_goals 
        try { 
          nlinarith 
        }
        <;> try { 
          tauto 
        }