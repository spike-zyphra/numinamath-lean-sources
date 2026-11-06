import Mathlib

open Real

theorem inequalities_167543 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (A G : ℝ) (hA : A = ∑ i, a i / n)
    (hG : G = (∏ i, a i) ^ ((1 : ℝ) / n)) :
    A ≥ G := by 
  rw [hA, hG]
  have h1 : (∑ i : Fin n, a i / n) ≥ (∏ i : Fin n, a i) ^ ((1 : ℝ) / n) := by
    have h3 : (∏ i : Fin n, a i) ^ ((1 : ℝ) / n) ≤ (∑ i : Fin n, (1 / n : ℝ) * (a i)) := by
      have h11 : ∏ j : Fin n, (a j) ^ (1 / n : ℝ) = (∏ i : Fin n, a i) ^ ((1 : ℝ) / n) := by
        rw [Real.finset_prod_rpow]
        all_goals
          try { 
            intro i hi
            have h8 : 0 ≤ a i := by linarith [ha i]
            exact h8
          }
          try { 
            simp 
          }
      have h10 : (∑ i : Fin n, (1 / n : ℝ) * (a i)) ≥ ∏ j : Fin n, (a j) ^ (1 / n : ℝ) := by
        apply Real.geom_mean_le_arith_mean_weighted
        all_goals
          try { 
            intro i hi
            have h7 : 0 < (1 / n : ℝ) := by
              have h3 : (n : ℝ) > 0 := by exact_mod_cast (show (0 : ℕ) < n by linarith [hn])
              positivity
            positivity
          }
          try { 
            intro i hi
            specialize ha i
            positivity
          }
          try { 
            have : ∑ i : Fin n, (1 / n : ℝ) = 1 := by
              calc 
                (∑ i : Fin n, (1 / n : ℝ)) = n * (1 / n : ℝ) := by 
                  simp [Finset.sum_const, Finset.card_univ]
                _ = 1 := by
                  field_simp
            linarith
          }
          try { 
            try simp 
          }
      have h11' : ∏ j : Fin n, (a j) ^ (1 / n : ℝ) = (∏ i : Fin n, a i) ^ ((1 : ℝ) / n) := h11
      linarith [h11', h10]
    have h12 : (∑ i : Fin n, (1 / n : ℝ) * (a i)) = (∑ i : Fin n, a i / n) := by
      congr
      funext i
      ring
    linarith [h12, h3]
  linarith