import Mathlib

theorem algebra_33262 (a : ℝ) (ha : a > 0) :
    (∃ x : ℤ, a ^ 3 * x ^ 3 + a ^ 2 * x ^ 2 + a * x + a = 0) ↔ a = 1 := by
  constructor
  · -- Assume ∃ x : ℤ, a ^ 3 * x ^ 3 + a ^ 2 * x ^ 2 + a * x + a = 0, prove a = 1
    rintro ⟨x, hx⟩
    have h1 : a ^ 3 * (x:ℝ) ^ 3 + a ^ 2 * (x:ℝ) ^ 2 + a * (x:ℝ) + a = 0 := by
      exact_mod_cast hx
    -- Factor the equation
    have h2 : a ^ 2 * (x:ℝ) ^ 3 + a * (x:ℝ) ^ 2 + (x:ℝ) + 1 = 0 := by
      have h2 : a > 0 := ha
      have h3 : a ^ 3 * (x:ℝ) ^ 3 + a ^ 2 * (x:ℝ) ^ 2 + a * (x:ℝ) + a = 0 := h1
      calc
        a ^ 2 * (x:ℝ) ^ 3 + a * (x:ℝ) ^ 2 + (x:ℝ) + 1
            = (a ^ 3 * (x:ℝ) ^ 3 + a ^ 2 * (x:ℝ) ^ 2 + a * (x:ℝ) + a) / a := by
                field_simp [ha.ne.symm]
                <;> ring
        _ = 0 / a := by rw [h1]
        _ = 0 := by norm_num
    -- Show x ≠ 0
    have h4 : x ≠ 0 := by
      by_contra h
      rw [h] at h2
      norm_num at h2
      all_goals nlinarith
    -- Show x < 0
    have h5 : (x:ℝ) < 0 := by
      by_contra h
      push_neg at h
      have hx0 : (x:ℝ) ≥ (0:ℝ) := by linarith
      -- Show that the polynomial is positive
      have h_pos : a ^ 2 * (x:ℝ) ^ 3 + a * (x:ℝ) ^ 2 + (x:ℝ) + 1 > 0 := by
        nlinarith [sq_nonneg (a * (x:ℝ)), sq_nonneg ((x:ℝ) * a), sq_nonneg ((x:ℝ)), sq_nonneg (a ^ 2 * (x:ℝ) ^ 0), sq_nonneg ((x:ℝ) ^ 2 * a), sq_nonneg ((x:ℝ) ^ 0 * a), sq_nonneg ((x:ℝ) * (x:ℝ) * a), sq_pos_of_pos ha, mul_pos ha (show 0 < a from by linarith), sq_nonneg (a - 1)]
      linarith
    -- Now x is negative integer
    have hx6 : x < 0 := by
      by_contra h
      push_neg at h
      have hx0 : x ≥ 0 := by omega
      have hx0' : (x:ℝ) ≥ (0:ℝ) := by exact_mod_cast hx0
      nlinarith
    -- Assume x < 0 integer, so x ≤ -1
    have h5' : x ≤ -1 := by
      by_contra h
      push_neg at h
      have hx0 : x ≥ 0 := by
          omega
      linarith
    -- Show x = -1 by bounds
    have h5' : x = -1 := by
      -- Show x ≤ -1
      have hx8 : x ≤ -1 := by
          by_contra h
          push_neg at h
          have hx0 : x ≥ 0 := by
              omega
          linarith
      -- Now show x ≥ -1
      have hx7 : x ≥ -1 := by
          by_contra h
          push_neg at h
          have hx11 : x ≤ -2 := by
              omega
          have hx12 : (x:ℝ) ≤ (-2:ℝ) := by
              exact_mod_cast hx11
          -- Show contradiction at x ≤ -2
          nlinarith [sq_nonneg ((x + 1:ℤ):ℝ), sq_nonneg ((x:ℝ) * a), sq_nonneg ((x:ℝ) ^ 2 * a ^ 2), sq_nonneg ((x +1:ℝ) * a ^ 2), sq_pos_of_pos ha, sq_nonneg (a * (x +1:ℝ)), sq_nonneg ((x * x:ℝ) * a * 1), sq_pos_of_pos (show 0 < a from by linarith), mul_pos ha (show 0 < a from by linarith), sq_nonneg (a -1)]
      -- Combine the bounds to get x = -1
      have : x = -1 := by
          omega
      assumption
    -- Substitute root x=-1 to get a=1
    rw [show (x:ℝ) = (-1:ℝ) by exact_mod_cast h5'] at h2
    nlinarith [sq_nonneg ((a:ℝ) -1), sq_nonneg ((a:ℝ) * (a:ℝ)), sq_nonneg ((a:ℝ) ^ 0)]
  · -- Assume a = 1, prove ∃ x : ℤ, a ^ 3 * x ^ 3 + a ^ 2 * x ^ 2 + a * x + a = 0
    intro h
    rw [h]
    use -1
    norm_num
  all_goals try { nlinarith }