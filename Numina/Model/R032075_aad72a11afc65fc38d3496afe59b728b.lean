import Mathlib
theorem algebra_611309 : IsGreatest {a : ℝ | ∃ x : ℝ, x > 0 ∧ a = (x ^ 2 + 2 - √(x ^ 4 + 4)) / x} (2 * √2 - 2):= by
  constructor
  · -- Show that 2 * √2 - 2 is achievable, with x = √2
    use Real.sqrt 2
    constructor
    · -- Show that √2 > 0
      positivity
    · -- Verify the value is equal to 2 * √2 - 2
      have h1 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h2 : (Real.sqrt 2 : ℝ) ^ 4 = 4 := by
        calc
          (Real.sqrt 2 : ℝ) ^ 4 = ((Real.sqrt 2 : ℝ) ^ 2) ^ 2 := by ring
          _ = 2 ^ 2 := by rw [h1]
          _ = 4 := by norm_num
      have h3 : √((Real.sqrt 2 : ℝ) ^ 4 + 4) = 2 * √2 := by
        rw [show (Real.sqrt 2 : ℝ) ^ 4 + 4 = (8 : ℝ) by
          rw [h2]
          all_goals norm_num]
        have h4 : √(8 : ℝ) = 2 * √2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf <;> norm_num [Real.sqrt_mul_self, Real.sq_sqrt]
          all_goals norm_num
        rw [h4]
        all_goals norm_num
        <;> ring_nf <;> norm_num [Real.sqrt_mul_self, Real.sq_sqrt]
        all_goals norm_num
      rw [h3]
      rw [h1]
      field_simp
      <;> ring_nf
      <;> field_simp
      <;> ring_nf
      <;> norm_num [Real.sqrt_mul_self, Real.sq_sqrt]
      all_goals norm_num
      all_goals ring_nf <;> norm_num [Real.sqrt_mul_self, Real.sq_sqrt]
      all_goals norm_num
      all_goals ring_nf <;> norm_num [Real.sqrt_mul_self, Real.sq_sqrt]
      all_goals norm_num
  · -- Show that 2 * √2 - 2 is greatest
    intro a ha
    rcases ha with ⟨x, hx, ha⟩
    have h2 : x > 0 := hx
    have h1 : (x ^ 2 + 2 - √(x ^ 4 + 4)) / x ≤ 2 * √2 - 2 := by
      have hx1 : x > 0 := h2
      have h3 : (x ^ 2 + 2 - √(x ^ 4 + 4)) ≤ (2 * √2 - 2) * x := by
        have h4 : √(x ^ 4 + 4) ≥ 0 := by positivity
        have h5 : x ^ 2 + 2 - (2 * √2 - 2) * x ≤ √(x ^ 4 + 4) := by
          have h6 : (x ^ 2 + 2 - (2 * √2 - 2) * x) ^ 2 ≤ x ^ 4 + 4 := by
            nlinarith [sq_nonneg (x ^ 2 - 2),
              sq_nonneg (x - √2),
              sq_nonneg (x ^ 2 - 2 * √2 + 2 * x),
              sq_nonneg (x * √2 - x * 2 - √2 + 2),
              Real.sqrt_nonneg (2 : ℝ),
              Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
              Real.sqrt_nonneg (2 : ℝ),
              Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
              sq_nonneg (x ^ 2 - 2 * √2 + 2 * x),
              sq_nonneg (x - √2),
              sq_nonneg ((2 * √2 - 2) * x - (x ^ 2 + 2)),
              sq_nonneg (x * √2 - 2 * x),
              Real.sqrt_nonneg (2 : ℝ),
              Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
            ]
          have h7 : (x ^ 2 + 2 - (2 * √2 - 2) * x) ≤ √(x ^ 4 + 4) := by
            nlinarith [Real.sqrt_nonneg (x ^ 4 + 4),
              Real.sq_sqrt (show (0 : ℝ) ≤ (x ^ 4 + 4 : ℝ) by positivity),
              h6, Real.sqrt_nonneg (2 : ℝ),
              Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
            ]
          linarith
        nlinarith [Real.sqrt_nonneg (x ^ 4 + 4), Real.sqrt_nonneg (2 : ℝ),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (x ^ 4 + 4 : ℝ) by positivity)
        ]
      have h6 : (x ^ 2 + 2 - √(x ^ 4 + 4)) / x ≤ 2 * √2 - 2 := by
        apply (div_le_iff₀ (by positivity)).mpr
        linarith
      linarith
    linarith [ha, h1]