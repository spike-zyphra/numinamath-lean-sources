import Mathlib

theorem inequalities_137805 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a * b * c = 1) :
    36 ≤ (a^2 + 1) * (b^3 + 2) * (c^6 + 5) := by

  have h1 : a ^ 2 + 1 ≥ 2 * a := by
    nlinarith [sq_nonneg (a - 1)]

  have h2 : b ^ 3 + 2 ≥ 3 * b := by
    nlinarith [sq_nonneg (b ^ 2 - 1), sq_nonneg (b - 1), sq_nonneg (b + 1), sq_nonneg (b * (b - 1)), sq_nonneg ((b - 1) * (b + 1)), mul_nonneg ha hb
    ]

  have h3 : c ^ 6 + 5 ≥ 6 * c := by
    nlinarith [sq_nonneg (c ^ 2 - 1), sq_nonneg (c - 1), sq_nonneg (c + 1), sq_nonneg (c ^ 3 - 1), sq_nonneg (c ^ 2 - c), sq_nonneg (c ^ 2 + c), sq_nonneg ((c - 1) * (c + 1)), sq_nonneg ((c ^ 2 - 1) * (c ^ 2 - 1)), sq_nonneg (c ^ 3 - c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc
    ]
  
  have h4 : (a^2 + 1) * (b^3 + 2) * (c^6 + 5) ≥ 36 * (a * b * c) := by
    have h4_a : a ^ 2 + 1 ≥ 2 * a := h1
    have h4_b : b ^ 3 + 2 ≥ 3 * b := h2
    have h4_c : c ^ 6 + 5 ≥ 6 * c := h3
    have h5 : (a^2 + 1) * (b^3 + 2) ≥ 6 * (a * b) := by
      nlinarith
    have h6 : (c^6 + 5) ≥ 6 * c := h4_c
    have h7 : (a^2 + 1) * (b^3 + 2) * (c^6 + 5) ≥ (6 * (a * b)) * (6 * c) := by
      have h8 : (a^2 + 1) * (b^3 + 2) ≥ 6 * (a * b) := h5
      have h9 : (c^6 + 5) ≥ 6 * c := h4_c
      have h10 : ((a^2 + 1) * (b^3 + 2)) * (c^6 + 5) ≥ (6 * (a * b)) * (6 * c) := by
        nlinarith [show (a * b) ≥ 0 by nlinarith, show (6 * c) ≥ 0 by nlinarith]
      linarith
    have h8 : (6 * (a * b)) * (6 * c) = 36 * (a * b * c) := by
      ring
    linarith [h7, h8
    ]

  have h5 : (a^2 + 1) * (b^3 + 2) * (c^6 + 5) ≥ 36 := by
    have h6 : (a^2 + 1) * (b^3 + 2) * (c^6 + 5) ≥ 36 * (a * b * c) := h4
    have h7 : a * b * c = 1 := habc
    have h8 : 36 * (a * b * c) = 36 := by
      rw [h7]
      all_goals norm_num
    linarith [h6, h8
    ]
  linarith [h5
  ]