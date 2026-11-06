import Mathlib

theorem algebra_252464 {h : ℕ → ℝ} (h0 : h 0 = 2)
    (hpos : ∀ n ≥ 1, h n > 0) (hdiff : ∀ n ≥ 1, (h n)^2 - 2 * (h (n - 1))^2 = 1) :
    ∀ n, h n = Real.sqrt (5 * 2^n - 1) := by
  intro n
  induction' n using Nat.strongRec with n ih
  cases n with
  | zero =>
    -- Base case n = 0
    -- Show h 0 = Real.sqrt (5 * 2 ^ 0 - 1)
    -- Which equals Real.sqrt 4
    -- Then Real.sqrt 4 = 2
    rw [h0]
    have h1 : Real.sqrt (5 * (2 : ℝ) ^ (0 : ℕ) - 1 : ℝ) = (2 : ℝ) := by
      norm_num [Real.sqrt_eq_iff_sq_eq]
      all_goals norm_num
      all_goals nlinarith
      all_goals try { linarith }
      all_goals try { ring_nf }
      all_goals try { linarith }
      all_goals try { tauto }
    rw [h1]
    <;> try { linarith } <;> try { norm_num } <;> try { tauto }
  | succ n =>
    have eq1 := hdiff (n + 1) (by linarith)
    simp [show n + 1 ≥ 1 by linarith] at eq1
    have h1 : h (n) = Real.sqrt (5 * (2 : ℝ) ^ (n : ℕ) - 1 : ℝ) := ih n (by linarith)
    have h1_sq : (h n) ^ 2 = (5 * (2 : ℝ) ^ (n : ℕ) - 1 : ℝ) := by
      calc
        (h n) ^ 2 = (Real.sqrt (5 * (2 : ℝ) ^ (n : ℕ) - 1 : ℝ)) ^ 2 := by rw [h1]
        _ = (5 * (2 : ℝ) ^ (n : ℕ) - 1 : ℝ) := by
          apply Real.sq_sqrt
          all_goals
            have : (5 : ℝ) * (2 : ℝ) ^ (n : ℕ) - 1 ≥ (0 : ℝ) := by
              have : (2 : ℝ) ^ (n : ℕ) ≥ (1 : ℝ) := by
                have h : (2 : ℝ) ^ (n : ℕ) ≥ (1 : ℝ) := by
                  apply one_le_pow₀
                  all_goals norm_num
                  all_goals linarith
                linarith
              nlinarith
            linarith
          all_goals try { linarith }
          all_goals try { tauto }
    have h2 : (h (n + 1)) ^ 2 = 1 + 2 * (h n) ^ 2 := by
      nlinarith
    have h3 : (h (n + 1)) ^ 2 = (5 * (2 : ℝ) ^ ((n + 1 : ℕ)) - 1 : ℝ) := by
      rw [h2]
      rw [h1_sq]
      ring_nf
      <;> try { linarith }
      <;> try { norm_num }
      <;> try { ring_nf }
      <;> try { linarith }
      <;> try { tauto }
    have h_pos : h (n + 1) > 0 := hpos (n + 1) (by linarith)
    have eq4 : h (n + 1) = Real.sqrt (5 * (2 : ℝ) ^ ((n + 1 : ℕ)) - 1 : ℝ) := by
      have h2_pos : (h (n + 1)) ^ 2 = (5 * (2 : ℝ) ^ (n + 1) - 1 : ℝ) := by
        nlinarith
      have h_eq : h (n + 1) = Real.sqrt ((h (n + 1)) ^ 2 : ℝ) := by
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_pos h_pos]
        all_goals try { linarith }
        all_goals try { tauto }
        all_goals try { rfl }
        all_goals try { linarith }
      rw [h_eq]
      rw [h2_pos]
      all_goals try { linarith }
      all_goals try { norm_num }
      all_goals try { tauto }
      all_goals try { linarith }
      all_goals try { tauto }
    simpa using eq4
    all_goals try { linarith }
    all_goals try { norm_num }
    all_goals try { tauto }
    all_goals try { linarith }
    all_goals try { tauto }