import Mathlib

open Real

theorem algebra_166648 {f : ℕ → ℝ → ℝ}
    (hf0 : ∀ x, f 0 x = 2 * sqrt x)
    (hfn : ∀ n, f (n + 1) = fun x => 4 / (2 - f n x)) :
    f 2023 4 = -2 := by

  have f04 : f 0 4 = 4 := by
    rw [hf0]
    have h2 : sqrt (4 : ℝ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    simp [h2]
    all_goals norm_num

  have f14 : f 1 4 = -2 := by
    have eq1 : f 1 = fun x => 4 / (2 - f 0 x) := by
      specialize hfn 0
      simpa using hfn 
    rw [eq1]
    simp only
    rw [f04]
    norm_num


  have f4 : ∀ (k : ℕ), f (3 * k + 1) 4 = -2 := by 
    intro k 
    induction k with 
    | zero =>
      norm_num 
      all_goals try { 
        simp [f14]
      }

    | succ k ih =>
      have eq2k2 : f (3 * k + 2) 4 = 1 := by
        have eq7 : f (3 * k + 2) = fun x => 4 / (2 - f (3 * k + 1) x) := by
          specialize hfn (3 * k + 1)
          simpa using hfn 
        rw [eq7]
        simp only
        rw [ih]
        norm_num

      have eq2k3 : f (3 * k + 3) 4 = 4 := by
        have eq8 : f (3 * k + 3) = fun x => 4 / (2 - f (3 * k + 2) x) := by
          specialize hfn (3 * k + 2)
          simpa using hfn
        rw [eq8]
        simp only
        rw [eq2k2]
        norm_num

      have eq2k4 : f (3 * (k + 1) + 1) 4 = -2 := by
        have eq2k4' : 3 * (k + 1) + 1 = 3 * k + 4 := by 
          omega 
        rw [eq2k4']
        have eq9 : f (3 * k + 4) = fun x => 4 / (2 - f (3 * k + 3) x) := by 
          specialize hfn (3 * k + 3)
          simpa using hfn 
        rw [eq9]
        simp only 
        rw [eq2k3]
        norm_num

      simpa using eq2k4 

  specialize f4 674
  norm_num at f4 ⊢ 
  all_goals try { 
    tauto 
  }