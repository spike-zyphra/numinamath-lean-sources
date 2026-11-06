import Mathlib

theorem algebra_302569 {a c : ℕ → ℝ} (ha : ∀ n, a n + a (n + 1) = -3 * n ∧ a n * a (n + 1) = c n)
    (ha1 : a 1 = 2) : c 100 = 22496 := by
  have h1 : ∀ (n : ℕ), a n + a (n + 1) = -3 * (n : ℝ) := by
    intro n
    have := (ha n).left
    simpa using this

  have h2 : ∀ (n : ℕ), a n * a (n + 1) = c n := by
    intro n 
    have := (ha n).right
    simpa using this

  have ha0 : a 0 = -2 := by
    have eq1 := h1 0
    norm_num at eq1 
    linarith [eq1, ha1]

  have eq3 : ∀ (n : ℕ), a n = -11 / 4 * (-1 : ℝ) ^ n - 3 / 2 * (n : ℝ) + 3 / 4 := by 
    intro n 
    induction n with 
    | zero =>
      rw [ha0]
      norm_num 
    | succ n ih =>
      have eq4' : a (n + 1) = -3 * (n : ℝ) - a n := by
        have eq5 : a n + a (n + 1) = -3 * (n : ℝ) := by 
          specialize h1 n 
          simpa using h1 
        linarith 
      rw [eq4']
      rw [ih]
      simp [pow_succ, pow_zero, mul_add, mul_sub]
      all_goals 
        ring_nf 
  have ha_100 : a 100 = -152 := by 
    specialize eq3 100
    norm_num at eq3 ⊢ 
    linarith [eq3]
  have ha_101 : a 101 = -148 := by 
    specialize eq3 101 
    norm_num at eq3 ⊢ 
    linarith [eq3]

  have eq4 : c 100 = a 100 * a 101 := by 
    specialize h2 100 
    have : a 100 * a (100 + 1) = c 100 := by 
      simpa using h2 
    have h7 : a (100 + 1) = a 101 := by 
      norm_num 
    rw [h7] at this 
    linarith 
  rw [eq4, ha_100, ha_101]
  norm_num