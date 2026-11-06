import Mathlib

theorem algebra_320285 (a b : ℝ) :
    (∃ x : ℝ, x^2 + 2 * (1 + a) * x + (3 * a^2 + 4 * a * b + 4 * b^2 + 2) = 0) ↔
    a = 1 ∧ b = -1 / 2 := by
  constructor
  · -- Assume there exists a real root.
    intro h
    rcases h with ⟨x, hx⟩
    have h : (2 * (1 + a)) ^ 2 - 4 * (1) * (3 * a^2 + 4 * a * b + 4 * b^2 + 2) ≥ 0 := by
      nlinarith [sq_nonneg (x + (1 + a)), sq_nonneg (x + 2 * (1 + a)), 
          sq_nonneg (a - 1), sq_nonneg (b + 1 / 2), 
          sq_nonneg (a + 2 * b), sq_nonneg (a - 1 + 2 * b), 
          sq_nonneg (x +1 + a), sq_nonneg (x +1 + a -2 * b)
        ]
    have h1 : -4 * (2 * a^2 + 4 * a * b + 4 * b^2 - 2 * a + 1) ≥ 0 := by
      nlinarith
    have h2 : 2 * a^2 + 4 * a * b + 4 * b^2 - 2 * a + 1 ≤ 0 := by
      nlinarith
    have eq1 : (a - 1)^2 = 0 := by 
      nlinarith [ sq_nonneg (a - 1), sq_nonneg (b + 1 / 2), sq_nonneg (2 * a - 2), sq_nonneg (2 * b + 1), 
          sq_nonneg (a - 1 - 2 * b), sq_nonneg ((a - (1)) + 2 * (b + 1 / 2))
        ]
    have eq_a : a = 1 := by
      nlinarith
    have eq2 : (b + 1 / 2)^2 = 0 := by 
      rw [eq_a] at h2 
      nlinarith [ sq_nonneg (b + 1 / 2), sq_nonneg (b - (-1 / 2))
      ]
    have eq_b : b = -1 / 2 := by 
      nlinarith
    exact ⟨eq_a, eq_b⟩
  · -- Show that if a = 1 and b = -1/2, then there exists a real root.
    rintro ⟨ha, hb⟩
    use -2 
    rw [ha, hb]
    norm_num