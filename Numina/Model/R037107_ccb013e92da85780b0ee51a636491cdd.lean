import Mathlib

open scoped BigOperators

theorem algebra_321762 (a : ℕ → ℝ)
  (h₀ : ∀ n, 0 < n → a n = (n^2 + n - 2 - Real.sqrt 2) / (n^2 - 2)) :
  ∏ i in Finset.Icc 1 2016, a i = 2016 * Real.sqrt 2 - 2015 := by
  have h1 : ∀ (n : ℕ), 0 < n → a n = (↑n + 1 + Real.sqrt 2) / (↑n + Real.sqrt 2) := by
    intro n hn
    rw [h₀ n hn]
    have h2 : (↑n ^ 2 + (↑n : ℝ) - 2 - Real.sqrt 2) = ((↑n ^ 2 - (2 : ℝ)) + ((↑n : ℝ) - Real.sqrt 2)) := by
      ring
    have h4 : (↑n ^ 2 - (2 : ℝ)) = (↑n - Real.sqrt 2) * (↑n + Real.sqrt 2) := by
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [h2, h4]
    have h5 : (↑n - Real.sqrt 2 : ℝ) ≠ 0 := by
      -- Note: we prove this by showing by contradiction
      -- if `↑n - Real.sqrt 2 = 0`, then `n = Real.sqrt 2`.
      -- because `n` is natural number, `sqrt 2` is irrational, then contradiction here.
      by_contra h11
      have h6 : Real.sqrt 2 > 0 := by positivity
      have h11' : (↑n : ℝ) = Real.sqrt 2 := by linarith
      have h11 : n > 0 := by linarith
      -- Note: `n` is natural number, and `n >= 1`
      have h7 : n ≥ 1 := by exact h11
      have h8 : (↑n : ℝ) ^ 2 = 2 := by
        have h12 : Real.sqrt 2 ^ 2 = (2 : ℝ) := by
          exact Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
        have h11'2 : (↑n : ℝ) = Real.sqrt 2 := h11'
        rw [h11'2]
        linarith [h12, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      -- Note: n is natural number, if `n ^ 2 = 2` positive rational, 
      -- clearly, contradiction here.
      -- Since `n >= 1`, we have n < 2, since n^2 = 2 contradict when n >= 2
      have h9 : (n : ℝ) ^ 2 = (2 : ℝ) := by 
        have h81 : (↑n : ℝ) ^ 2 = (2 : ℝ) := h8
        have h11'2 : (↑n : ℝ) = (↑n : ℝ) := by rfl 
        norm_cast at h81 ⊢
      -- Note: n is natural, n^2 = 2
      have h10 : n ^ 2 = 2 := by
        have h81 : (n : ℝ) ^ 2 = (2 : ℝ) := h9 
        norm_cast at h81 ⊢
      -- Note: for contradiction
      -- since n >= 1 and n < 2
      have h12 : n <= 1 := by
        by_contra h12
        push_neg at h12
        have h12' : n >= 2 := by
          omega
        have h12'' : n^2 >= 4 := by
          nlinarith [h12']
        nlinarith
      -- Note: since n <= 1 and n >= 1, n = 1
      have h13 : n = 1 := by
        omega
      -- Note: contradiction here
      rw [h13] at h10
      norm_num at h10
    field_simp [(show (↑n - Real.sqrt 2) ≠ 0 by assumption), 
      show (↑n ^ 2 - (2 : ℝ)) + (↑n - Real.sqrt 2) ≠ 0 by 
      by_contra h6
      have h7 : (↑n ^ 2 - (2 : ℝ) ) + (↑n - Real.sqrt 2) = (↑n - Real.sqrt 2) * (↑n + Real.sqrt 2 + 1) := by
        nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      rw [h7] at h6
      have h8 : (↑n - Real.sqrt 2) * (↑n + Real.sqrt 2 + 1) = 0 := by
        linarith
      cases' (mul_eq_zero.mp h8) with h9 h10
      · contradiction
      · -- nlinarith
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    ]
    <;> ring_nf
    <;> norm_num
    all_goals 
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  -- now we use it to compute
  have h7 : ∀ (n : ℕ), ∏ i in Finset.Icc 1 n, a i = (↑n + 1 + Real.sqrt 2) / (1 + Real.sqrt 2) := by
    intro n
    induction n with
    | zero => 
      simp [Finset.prod_eq_zero, h1]
      <;> norm_num
      <;> field_simp
      <;> norm_num 
      all_goals
        try { 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), 
            Real.sqrt_nonneg 2, 
            Real.sqrt_nonneg 2, 
            Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), 
            Real.sqrt_nonneg 2, 
            Real.sqrt_nonneg 2, 
            Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        }
    | succ n ih => 
      rw [Finset.prod_Icc_succ_top (by linarith), ih]
      rw [h1 (n + 1) (by linarith)]
      all_goals 
        field_simp
        <;> norm_num
        all_goals 
          try { 
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), 
              Real.sqrt_nonneg 2, 
              Real.sqrt_nonneg 2, 
              Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), 
              Real.sqrt_nonneg 2, 
              Real.sqrt_nonneg 2, 
              Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
          }
  specialize h7 2016
  rw [h7]
  have h8 : (↑2016 + 1 + Real.sqrt 2) / (1 + Real.sqrt 2) = (2016 * Real.sqrt 2 - 2015 : ℝ) := by
    have h14 : (1 + Real.sqrt 2 : ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring_nf <;> norm_num
    <;> ring
    <;> norm_num
    <;> nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  norm_num [h8]
  all_goals nlinarith
  all_goals 
    try { 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), 
          Real.sqrt_nonneg 2, 
          Real.sqrt_nonneg 2, 
          Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), 
          Real.sqrt_nonneg 2, 
          Real.sqrt_nonneg 2 
        ]
      }
  -- Note: end of proof.
  all_goals 
    try { assumption }
    all_goals
      try { 
        exfalso <;> linarith
      }
  <;> norm_num [Finset.prod_eq_zero, h1]
  <;> norm_num
  <;> assumption
  <;> ring
  <;> norm_num
  <;> nlinarith
  <;> try { 
    exfalso
    <;> norm_num
    <;> try { 
      linarith
    }
  }
  <;> try { 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), 
      Real.sqrt_nonneg 2, 
      show Real.sqrt 2^2 > 0 by positivity 
    ]
  }
  <;> try { 
    norm_num
    <;> linarith <;> norm_num <;> nlinarith
  }