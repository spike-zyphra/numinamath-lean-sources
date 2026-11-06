import Mathlib

theorem algebra_630316 (a b : ℤ) (has_real_root : ∃ x : ℝ, (1/4) * x^2 - a * x + a^2 + a * b - a - b - 1 = 0) (eq_roots : ∀ (x y : ℝ), ((1/4) * x^2 - a * x + a^2 + a * b - a - b - 1 = 0) → ((1/4) * y^2 - a * y + a^2 + a * b - a - b - 1 = 0) → x = y) : a - b = 1 ∨ a - b = -1 := by

  rcases has_real_root with ⟨x, hx⟩
  have h_eq1 : (1/4) * (4 * (a : ℝ) - x) ^ 2 - a * (4 * (a : ℝ) - x) + a^2 + a * (b : ℝ) - a - b - 1 = 0 := by
    nlinarith [sq_nonneg (x - 2 * (a : ℝ)), sq_nonneg ((x - (4 * (a : ℝ) - x)) / 2)]
  have h_eq2 : 4 * (a : ℝ) - x = x := by
    apply eq_roots
    all_goals
    try tauto
  have h_x : x = (2 * (a : ℝ)) := by
    nlinarith
  rw [h_x] at hx
  have h_eq3 : (a : ℝ) * ( (b : ℝ) ) - (a : ℝ) - (b : ℝ) = (1 : ℝ) := by
    nlinarith
  have h_eq4 : (a * (b : ℤ) - a - b) = 1 := by
    exact_mod_cast h_eq3
  -- (a - 1)(b - 1) = 2 
  have h_eq5 : (a - 1) * (b - 1) = 2 := by
    nlinarith [h_eq4]
  have h2 : a - 1 ∣ 2 := by
    use (b - 1)
    all_goals nlinarith [h_eq5]
  have h3 : a - 1 = 1 ∨ a - 1 = 2 ∨ a - 1 = -1 ∨ a - 1 = -2 := by 
    have h4 : a - 1 ∣ 2 := h2
    have h5 : a - 1 = 1 ∨ a - 1 = 2 ∨ a - 1 = -1 ∨ a - 1 = -2 := by
      have h6 : a - 1 ∣ 2 := h4
      have h7 : a - 1 ≤ 2 := by
        exact Int.le_of_dvd (by norm_num) h6
      have h8 : a - 1 ≥ -2 := by
        have h9 : (- (a - 1) ) ∣ 2 := by 
          exact Int.neg_dvd.2 h6
        have h10 : - (a - 1) ≤ 2 := by 
          exact Int.le_of_dvd (by norm_num) h9 
        linarith 
      interval_cases (a - 1) <;> try tauto 
    exact h5 
  rcases h3 with (h | h | h | h)
  all_goals
  try { 
    -- Compute the value of b from h_eq5
    have h4 : b - 1 = 2 := by 
      nlinarith [h_eq5, h]
    have h5 : b = 3 := by 
      linarith [h4]
    have h6 : a = 2 := by 
      linarith [h]
    right
    omega 
  }
  all_goals 
  try { 
    have h4 : b - 1 = 1 := by 
      nlinarith [h_eq5, h]
    have h5 : b = 2 := by 
      linarith [h4]
    have h6 : a = 3 := by 
      linarith [h]
    left
    omega 
  }
  all_goals 
  try { 
    have h4 : b - 1 = -2 := by 
      nlinarith [h_eq5, h]
    have h5 : b = -1 := by 
      linarith [h4]
    have h6 : a = 0 := by 
      linarith [h]
    left
    omega 
  }
  all_goals 
  try { 
    have h4 : b - 1 = -1 := by 
      nlinarith [h_eq5, h]
    have h5 : b = 0 := by 
      linarith [h4]
    have h6 : a = -1 := by 
      linarith [h]
    right
    omega 
  }