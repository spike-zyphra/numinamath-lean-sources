import Mathlib

theorem number_theory_211731 {f : ℕ → ℕ} (hpos : ∀ n, 0 < n → f n ≥ 0)
    (hmul : ∀ m n, f (m * n) = f m + f n) (hf : ∀ n, n % 10 = 3 → f n = 0)
    (hf' : f 10 = 0) : f 1985 = 0 := by

  have h2_5 : f 10 = f 2 + f 5 := by 
    have h2 : f 10 = f 2 + f 5 := by 
      calc 
        f 10 = f (2 * 5) := by norm_num 
        _ = f 2 + f 5 := by rw [hmul 2 5]
    exact h2

  have eq1 : f 2 + f 5 = 0 := by 
    omega

  have eq2 : f 2 ≥ 0 := by 
    apply hpos 
    all_goals norm_num

  have eq3 : f 5 ≥ 0 := by 
    apply hpos 
    all_goals norm_num

  have h5 : f 5 = 0 := by
    omega

  have h1 : f 1985 = f 5 + f 397 := by 
    calc 
      f 1985 = f (5 * 397) := by norm_num 
      _ = f 5 + f 397 := by rw [hmul 5 397]

  have h3 : f 3573 = 0 := by 
    apply hf 
    all_goals norm_num

  have eq4 : f 3573 = f 397 + f 9 := by 
    calc 
      f 3573 = f (397 * 9) := by norm_num 
      _ = f 397 + f 9 := by rw [hmul 397 9]

  have eq5 : f 397 + f 9 = 0 := by 
    omega

  have eq6 : f 397 ≥ 0 := by 
    apply hpos 
    all_goals norm_num

  have eq7 : f 9 ≥ 0 := by 
    apply hpos 
    all_goals norm_num

  have h9 : f 397 = 0 := by
    omega

  omega