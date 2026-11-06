import Mathlib

theorem algebra_12108 {a : ℕ → ℝ} (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, 4 * a (n + 1) - a (n + 1) * a n + 4 * a n = 9) :
    a 2018 = 5 / 3 := by

  have ha2 : a 2 = 5 / 3 := by 
    have eq1 := han 1 (by norm_num)
    simp [ha1] at eq1 
    linarith

  have ha3 : a 3 = 1 := by
    have eq1 := han 2 (by norm_num)
    simp [ha2] at eq1 
    nlinarith

  have ha4 : a 4 = 5 / 3 := by 
    have eq1 := han 3 (by norm_num)
    simp [ha3] at eq1 
    linarith

  have h1 : ∀ n : ℕ, a (2 * n + 1) = 1 := by 
    intro n 
    induction n with 
    | zero => 
      norm_num [ha1]
    | succ n ih => 
      have eq1 := han (2 * n + 1) (by linarith)
      have eq2 := han (2 * n + 2) (by linarith)
      simp only [show 2 * n + 1 + 1 = 2 * n + 2 by omega, ih] at eq1 
      have eq_a2n2 : a (2 * n + 2) = 5 / 3 := by 
        linarith
      simp [show 2 * n + 2 + 1 = 2 * n + 3 by omega, eq_a2n2] at eq2 
      have eq3 : a (2 * (n + 1) + 1) = a (2 * n + 3) := by 
        ring_nf 
      have eq4 : a (2 * n + 3) = 1 := by 
        -- From eq2 : 4 * a(2*n+3) - a(2*n+3)*(5/3) + 4*(5/3) = 9
        -- We need to show a(2*n+3) = 1
        have eq5 : (4 * a (2 * n + 3) - a (2 * n + 3) * (5 / 3) + 4 * (5 / 3)) * 3 = (9 : ℝ) * 3 := by
          rw [eq2]
          all_goals
            norm_num
        ring_nf at eq5 
        have eq6 : a (2 * n + 3) = 1 := by 
          nlinarith 
        exact_mod_cast eq6 
      rw [eq3]
      linarith [eq4]

  have h2 : ∀ n : ℕ, a (2 * n + 2) = 5 / 3 := by
    intro n 
    induction n with
    | zero => 
      norm_num [ha2]
    | succ n ih => 
      have eq1 := han (2 * n + 2) (by linarith)
      have eq2 := han (2 * n + 3) (by linarith)
      simp only [show 2 * n + 2 + 1 = 2 * n + 3 by omega, ih] at eq1 
      have eq3 : a (2 * n + 3) = 1 := by 
        nlinarith 
      simp [show 2 * n + 3 + 1 = 2 * n + 4 by omega, eq3] at eq2 
      have eq4 : a (2 * (n + 1) + 2) = a (2 * n + 4) := by 
        ring_nf 
      have eq5 : a (2 * n + 4) = 5 / 3 := by 
        -- From eq2 : 4 * a(2*n+4) - a(2*n+4) + 4 = 9
        -- We need to show a(2*n+4) = 5/3
        have eq6 : (4 * a (2 * n + 4) - a (2 * n + 4) + 4) * 3 = (9 : ℝ) * 3 := by 
          rw [eq2]
          all_goals 
            norm_num
        ring_nf at eq6 
        have eq7 : a (2 * n + 4) = 5 / 3 := by 
          linarith 
        exact_mod_cast eq7 
      rw [eq4]
      linarith [eq5]

  have : 2018 = 2 * 1008 + 2 := by 
    omega

  rw [this]
  specialize h2 1008
  linarith