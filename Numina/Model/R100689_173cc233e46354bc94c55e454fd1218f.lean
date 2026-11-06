import Mathlib

theorem algebra_242560 (x : ℝ) (hx : x^2 - 8 * ⌊x⌋ + 7 = 0) :
    x = 1 ∨ x = Real.sqrt 33 ∨ x = Real.sqrt 41 ∨ x = 7 := by
  let n := ⌊x⌋
  have h1 : (x : ℝ) ^ 2 = 8 * (n : ℝ) - 7 := by
    have h_eq : (n : ℝ) = (⌊x⌋ : ℝ) := by simp [n]
    have h_eq2 : (n : ℝ) = (⌊x⌋ : ℝ) := by simp [n]
    have h_eq3 : (n : ℝ) = (⌊x⌋ : ℝ) := by simp [n]
    have h_eq4 : (n : ℝ) = (⌊x⌋ : ℝ) := by simp [n]
    linarith
  have h2 : (n : ℝ) ≤ x := by exact Int.floor_le x
  have h3 : x < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
  have h4 : 8 * (n : ℝ) - 7 ≥ 0 := by nlinarith [sq_nonneg (x : ℝ)]
  have h5 : n ≥ 1 := by
    by_contra h
    push_neg at h
    have hn1 : n ≤ 0 := by omega
    have hn2 : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hn1
    nlinarith
  have h6 : n ≤ 7 := by
    by_contra h
    push_neg at h
    have hn1 : n ≥ 8 := by omega
    have hn2 : (n : ℝ) ≥ (8 : ℝ) := by exact_mod_cast hn1
    nlinarith [sq_nonneg (x - (8 : ℝ)), sq_nonneg (x + (8 : ℝ))]
  have h7 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases h7 with h7 | h7 | h7 | h7 | h7 | h7 | h7
  · -- Case n = 1
    have hn1 : (n : ℝ) = (1 : ℝ) := by exact_mod_cast h7
    have hx1 : x ^ 2 = (1 : ℝ) := by
      nlinarith [h1, hn1]
    have hx2 : x = (1 : ℝ) := by
      nlinarith [h2, h3, hn1, sq_nonneg (x - (1 : ℝ)), sq_nonneg (x + (1 : ℝ))]
    left
    exact_mod_cast hx2
  · -- Case n = 2
    have hn2 : (n : ℝ) = (2 : ℝ) := by exact_mod_cast h7
    have hx1 : x ^ 2 = (9 : ℝ) := by
      nlinarith [h1, hn2]
    have h2_1 : (2 : ℝ) ≤ x := by
      linarith [h2, hn2]
    have h2_2 : x < (3 : ℝ) := by
      linarith [h3, hn2]
    nlinarith [sq_nonneg (x - (3 : ℝ)), sq_nonneg (x + (3 : ℝ)), hx1, h2_1, h2_2]
  · -- Case n = 3
    have hn3 : (n : ℝ) = (3 : ℝ) := by exact_mod_cast h7
    have hx1 : x ^ 2 = (17 : ℝ) := by
      nlinarith [h1, hn3]
    have h3_1 : (3 : ℝ) ≤ x := by
      linarith [h2, hn3]
    have h3_2 : x < (4 : ℝ) := by
      linarith [h3, hn3]
    nlinarith [sq_nonneg (x - (4 : ℝ)), sq_nonneg (x + (4 : ℝ)), hx1, h3_1, h3_2]
  · -- Case n = 4
    have hn4 : (n : ℝ) = (4 : ℝ) := by exact_mod_cast h7
    have hx1 : x ^ 2 = (25 : ℝ) := by
      nlinarith [h1, hn4]
    have h4_1 : (4 : ℝ) ≤ x := by
      linarith [h2, hn4]
    have h4_2 : x < (5 : ℝ) := by
      linarith [h3, hn4
      ]
    nlinarith [sq_nonneg (x - (5 : ℝ)), sq_nonneg (x + (5 : ℝ)), hx1, h4_1, h4_2
    ]
  · -- Case n = 5
    have hn5 : (n : ℝ) = (5 : ℝ) := by exact_mod_cast h7
    have hx1 : x ^ 2 = (33 : ℝ) := by
      nlinarith [h1, hn5
      ]
    have hx2 : x = Real.sqrt 33 := by
      have h4 : x ^ 2 = (33 : ℝ) := by
        nlinarith [h1, hn5
        ]
      have hx3 : x ≥ (5 : ℝ) := by
        linarith [h2, hn5
        ]
      have hx4 : x < (6 : ℝ) := by
        linarith [h3, hn5
        ]
      have h5 : x ≥ 0 := by
        linarith [h2, hn5
        ]
      have h6 : (Real.sqrt 33 : ℝ) ≥ 0 := Real.sqrt_nonneg 33
      have h7 : (Real.sqrt 33 : ℝ) ^ 2 = (33 : ℝ) := Real.sq_sqrt (by norm_num
      )
      nlinarith [h4, h7, h5, hx4
      ]
    right
    left
    exact_mod_cast hx2
  · -- Case n = 6
    have hn6 : (n : ℝ) = (6 : ℝ) := by exact_mod_cast h7
    have hx1 : x ^ 2 = (41 : ℝ) := by
      nlinarith [h1, hn6
      ]
    have hx2 : x = Real.sqrt 41 := by
      have h4 : x ^ 2 = (41 : ℝ) := by
        nlinarith [h1, hn6
        ]
      have hx3 : x ≥ (6 : ℝ) := by
        linarith [h2, hn6
        ]
      have hx4 : x < (7 : ℝ) := by
        linarith [h3, hn6
        ]
      have h5 : x ≥ 0 := by
        linarith [h2, hn6
        ]
      have h6 : (Real.sqrt 41 : ℝ) ≥ 0 := Real.sqrt_nonneg 41
      have h7 : (Real.sqrt 41 : ℝ) ^ 2 = (41 : ℝ) := Real.sq_sqrt (by norm_num
      )
      nlinarith [h4, h7, h5, hx4
      ]
    right
    right
    left
    exact_mod_cast hx2
  · -- Case n = 7
    have hn7 : (n : ℝ) = (7 : ℝ) := by exact_mod_cast h7
    have hx1 : x ^ 2 = (49 : ℝ) := by
      nlinarith [h1, hn7
      ]
    have hx2 : x = (7 : ℝ) := by
      nlinarith [h2, h3, hn7, sq_nonneg (x - (7 : ℝ)), sq_nonneg (x + (7 : ℝ))
      ]
    right
    right
    right
    exact_mod_cast hx2