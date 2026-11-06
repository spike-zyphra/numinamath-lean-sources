import Mathlib
theorem inequalities_607357 (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : n ≤ x) :
x + n / x ≥ n + 1 ∧ (x + n / x = n + 1 ↔ x = n):= by
  have hn1 : (n : ℝ) > 0 := by
    exact_mod_cast hn
  have h1 : x ≥ (n : ℝ) := by
    exact_mod_cast hx
  have hn3 : (n : ℝ) ≥ (1 : ℝ) := by
    have hn2 : n ≥ 1 := by
      linarith
    exact_mod_cast hn2
  constructor
  · -- First part: Show the inequality
    have hx4 : x + (n : ℝ) / x ≥ (n + 1 : ℝ) := by
      have hx4 : x > (0 : ℝ) := by
        nlinarith [hn3, h1]
      have hx2 : x + (n : ℝ) / x - (n + 1 : ℝ) ≥ (0 : ℝ) := by
        have hx2' : x + (n : ℝ) / x - (n + 1 : ℝ) = (x ^ 2 + (n : ℝ) - (n + 1 : ℝ) * x ) / x := by
          field_simp
          <;> nlinarith
        rw [hx2']
        apply div_nonneg
        -- Show that the numerator is non-negative
        have h2 : x ^ 2 + (n : ℝ) - (n + 1 : ℝ) * x ≥ (0 : ℝ) := by
          have hn4 : (n : ℝ) ≥ (1 : ℝ) := hn3
          nlinarith [sq_nonneg (x - (n : ℝ)), sq_nonneg (x - (1 : ℝ)), 
            mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (show (n : ℝ) ≥ (1 : ℝ) by linarith))
          ]
        linarith
        -- Show that the denominator is positive
        all_goals linarith
      linarith
    linarith
  · -- Second part: Equality holds iff x = n
    constructor
    · -- Assume equality holds, prove x = n
      intro h_eq
      have hx4 : x > (0 : ℝ) := by
        nlinarith [hn3, h1]
      have h3 : x + (n : ℝ) / x = n + 1 := by
        linarith [h_eq
        ]
      have hx5 : x ^ 2 + (n : ℝ) = (n + 1 : ℝ) * x := by
        have hx6 : x > 0 := hx4
        field_simp at h3
        nlinarith
      have hn4 : (n : ℝ) ≥ (1 : ℝ) := by
        have hn5 : n ≥ 1 := by linarith
        exact_mod_cast hn5
      have hn5 : (x - (n : ℝ)) * (x - (1 : ℝ)) = 0 := by
        nlinarith [hx5, hn4
        ]
      cases' (mul_eq_zero.mp hn5) with h13 h14
      · -- Case where x - n = 0
        have hx6 : x = (n : ℝ) := by
          linarith
        exact_mod_cast hx6
      · -- Case where x - 1 = 0
        have hx7 : x = (1 : ℝ) := by
          linarith
        have hn5 : (n : ℝ) = (1 : ℝ) := by
          nlinarith [h1, hn4, hx7
          ]
        have hn6 : n = 1 := by
          exact_mod_cast hn5
        have hx8 : x = (n : ℝ) := by
          nlinarith [hn6, hx7
          ]
        exact_mod_cast hx8
    · -- Assume x = n, prove equality
      intro h_eq
      rw [h_eq]
      field_simp
      <;> nlinarith