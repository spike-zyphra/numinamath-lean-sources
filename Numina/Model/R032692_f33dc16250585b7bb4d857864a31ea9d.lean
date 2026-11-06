import Mathlib

theorem algebra_165214 {a q : ℝ} (hq : |q| < 1) (hsum : ∑' n : ℕ, a * q ^ n = 4)
    (hcube : ∑' n : ℕ, (a * q ^ n) ^ 3 = 192) :
    a = 6 ∧ q = -1 / 2 := by
  have h1 : ∑' n : ℕ, a * q ^ n = a / (1 - q) := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring
    · exact hq
  rw [h1] at hsum
  have h2 : ∑' n : ℕ, (a * q ^ n) ^ 3 = a ^ 3 / (1 - q ^ 3) := by
    have h3 : ∑' n : ℕ, (a * q ^ n) ^ 3 = ∑' n : ℕ, a ^ 3 * (q ^ 3) ^ n := by
      congr 1
      funext n
      ring_nf
    rw [h3]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring
    · -- Show that |q^3| < 1
      have h4 : |q ^ 3| < 1 := by
        have h5 : |q ^ 3| = |q| ^ 3 := by
          simp [abs_pow]
        rw [h5]
        have h6 : |q| ^ 3 < (1 : ℝ) := by
          have h7 : |q| < (1 : ℝ) := hq
          have h8 : |q| ≥ 0 := by apply abs_nonneg
          nlinarith [sq_nonneg (|q|), sq_nonneg (|q| - 1), pow_pos (show (0 : ℝ) < 1 - |q| by linarith) 3]
        linarith
      exact h4
  rw [h2] at hcube
  have hne : a ≠ 0 := by
    by_contra h
    rw [h] at hsum
    have hne1 : (1 - q) ≠ 0 := by
      by_contra h11
      have h12 : q = 1 := by linarith
      rw [h12] at hq
      norm_num [abs] at hq
      all_goals try { tauto }
    field_simp [hne1] at hsum
    all_goals nlinarith
    all_goals try { tauto }
  -- From the first equation, we can solve for a: a = 4(1 - q)
  have eq3 : a = 4 * (1 - q) := by
    have hne1 : 1 - q ≠ 0 := by
      by_contra h11
      have h12 : q = 1 := by linarith
      rw [h12] at hq
      norm_num [abs] at hq
      all_goals try { tauto }
    have eq4 : a = 4 * (1 - q) := by
      field_simp [hne1] at hsum
      nlinarith
    linarith
  -- Substitute into the second equation: 64 * (1 - q)^3 / (1 - q^3) = 192
  have eq6 : 1 - q ^ 3 ≠ 0 := by
    by_contra h14
    have h8 : q ^ 3 = 1 := by linarith
    have h9 : |q| = 1 := by
      have h10 : |q ^ 3| = |(1 : ℝ)| := by
        rw [h8]
      have h11 : |q ^ 3| = |q| ^ 3 := by
        rw [abs_pow]
      rw [h11] at h10
      norm_num at h10
      have h12 : |q| = 1 := by
        have h13 : |q| ^ 3 - 1 = 0 := by
          nlinarith
        have h14 : (|q| - 1) * (|q| ^ 2 + |q| + 1) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h14) with h15 h16
        · -- Case where |q| - 1 = 0
          linarith
        · -- Case where |q| ^ 2 + |q| + 1 = 0
          nlinarith [sq_nonneg (|q| + 1 / 2)]
      linarith
    linarith [abs_lt.mp hq, h9]
  rw [eq3] at hcube
  have eq8 : (2 * q ^ 3 + 3 * q ^ 2 - 3 * q - 2) = 0 := by
    have eq9 : 1 - q ≠ 0 := by
      by_contra h
      have h11 : q = 1 := by linarith
      rw [h11] at hq
      norm_num [abs] at hq
      all_goals try { tauto }
    -- Use eq6 from previous step
    field_simp [eq9, eq6] at hsum hcube
    nlinarith [sq_nonneg (q + 1 / 2), sq_nonneg (q - 1), sq_nonneg (q * (q - 1)), sq_nonneg (q * (q + 1 / 2)), sq_pos_of_pos (show 0 < 1 - q by
        have hq' : |q| < 1 := hq
        have h2 : q < 1 := by linarith [abs_lt.mp hq' ]
        nlinarith
      )
    ]
  -- Factor the cubic polynomial
  have factored : (q + 2) * (2 * q + 1) * (q - 1) = 0 := by
    nlinarith [eq8]
  cases' (mul_eq_zero.mp factored) with h10 h11
  cases' (mul_eq_zero.mp h10) with h12 h13
  · -- Case where q + 2 = 0, so q = -2
    have h14 : q = -2 := by linarith
    have h15 : |q| = 2 := by
      rw [h14]
      norm_num [abs]
    linarith [abs_lt.mp hq, h15]
  · -- Case where 2q + 1 = 0, so q = -1/2
    have h15 : q = -1 / 2 := by linarith
    have h16 : a = 6 := by
      rw [h15] at eq3
      nlinarith
    constructor
    · -- Show that a = 6
      linarith [h16]
    · -- Show that q = -1/2
      linarith [h15]
  · -- Case where q - 1 = 0, so q = 1
    have h14 : q = 1 := by linarith
    have h15 : |q| = 1 := by
      rw [h14]
      norm_num [abs]
    linarith [abs_lt.mp hq, h15]