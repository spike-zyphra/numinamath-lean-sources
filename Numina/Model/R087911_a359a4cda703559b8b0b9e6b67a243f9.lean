import Mathlib

theorem algebra_13589 : IsLeast {k : ℤ | 0 < k ∧ ∃ x : ℝ, (3 * k + 2) * x ^ 2 + (k - 2) * x - 1 = 0} 1 := by
  constructor
  · constructor
    · norm_num
    · -- Show there's a solution when k = 1
      use (1 + Real.sqrt 21)/10
      norm_num
      ring_nf
      rw [Real.sq_sqrt (by norm_num)]
      linarith
  · -- Prove that 1 is the least integer
    intro k hk
    rcases hk with ⟨hk_pos, h_eq⟩
    rcases h_eq with ⟨x, hx⟩
    have h1 : (k : ℝ) > 0 := by exact_mod_cast hk_pos
    have h2 : ((3 * k + 2 : ℝ)) * x ^ 2 + ((k - 2 : ℝ)) * x - 1 = 0 := by
      simpa using hx
      -- rewrite quadratic equation
    have h3 : ((k : ℝ) - 2) ^ 2 - 4 * ((3 * k + 2) : ℝ) * (-1) ≥ 0 := by
      nlinarith [sq_nonneg ((3 * k + 2 : ℝ) * x), sq_nonneg ((k - 2 : ℝ) - (3 * k + 2) * x * 2), sq_nonneg (x), sq_nonneg ((k - 2 : ℝ))]
      -- rewrite discriminant when reflect about linear algebra square.
    -- derive explict quadratic inequality
    have h4 : ((k - 2) : ℝ) ^ 2 - 4 * ((3 * k + 2) : ℝ) * (-1) = (k : ℝ) ^ 2 + 8 * (k : ℝ) + 12 := by
      nlinarith
    rw [h4] at h3
    -- clearly 0 = degree discriminant
    have h5 : (k : ℝ) ^ 2 + 8 * (k : ℝ) + 12 ≥ 0 := by
      linarith
    -- prove k is !=0
    have h6 : k ^ 2 + 8 * k + 12 ≥ 0 := by
      exact_mod_cast h5
    by_contra h
    push_neg at h
    have h7 : k < 1 := by omega
    interval_cases k <;> omega
    all_goals
      nlinarith