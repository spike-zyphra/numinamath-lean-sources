import Mathlib

theorem algebra_321434 {a b c d : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : a * b * c * d ≠ 0) :
    (a / abs a + b / abs b + c / abs c + d / abs d - a * b / abs (a * b) - a * c / abs (a * c) -
     a * d / abs (a * d) - b * c / abs (b * c) - b * d / abs (b * d) - c * d / abs (c * d) +
     a * b * c / abs (a * b * c) + a * b * d / abs (a * b * d) + a * c * d / abs (a * c * d) +
     b * c * d / abs (b * c * d) - a * b * c * d / abs (a * b * c * d)) = 1 ∨
    (a / abs a + b / abs b + c / abs c + d / abs d - a * b / abs (a * b) - a * c / abs (a * c) -
     a * d / abs (a * d) - b * c / abs (b * c) - b * d / abs (b * d) - c * d / abs (c * d) +
     a * b * c / abs (a * b * c) + a * b * d / abs (a * b * d) + a * c * d / abs (a * c * d) +
     b * c * d / abs (b * c * d) - a * b * c * d / abs (a * b * c * d)) = -15 := by

  have ha1 : a / abs a = 1 ∨ a / abs a = -1 := by
    cases (le_or_lt 0 a) with
    | inl h1 =>
      have h2 : abs a = a := abs_of_nonneg h1
      left
      field_simp [h2, ha]
    | inr h2 =>
      have h3 : abs a = -a := abs_of_neg h2
      right
      field_simp [h3, ha]

  have hb1 : b / abs b = 1 ∨ b / abs b = -1 := by
    cases (le_or_lt 0 b) with
    | inl h1 =>
      have h2 : abs b = b := abs_of_nonneg h1
      left
      field_simp [h2, hb]
    | inr h2 =>
      have h3 : abs b = -b := abs_of_neg h2
      right
      field_simp [h3, hb]

  have hc1 : c / abs c = 1 ∨ c / abs c = -1 := by
    cases (le_or_lt 0 c) with
    | inl h1 =>
      have h2 : abs c = c := abs_of_nonneg h1
      left
      field_simp [h2, hc]
    | inr h2 =>
      have h3 : abs c = -c := abs_of_neg h2
      right
      field_simp [h3, hc]

  have hd1 : d / abs d = 1 ∨ d / abs d = -1 := by
    cases (le_or_lt 0 d) with
    | inl h1 =>
      have h2 : abs d = d := abs_of_nonneg h1
      left
      field_simp [h2, hd]
    | inr h2 =>
      have h3 : abs d = -d := abs_of_neg h2
      right
      field_simp [h3, hd]

  have h1 : a * b / abs (a * b) = (a / abs a) * (b / abs b) := by
    have h2 : abs (a * b) = abs a * abs b := by
      simp [abs_mul]
    rw [h2]
    field_simp [ha, hb, show a * b ≠ 0 by
      apply mul_ne_zero
      exact ha
      exact hb
    ]

  have h2 : a * c / abs (a * c) = (a / abs a) * (c / abs c) := by
    have h3 : abs (a * c) = abs a * abs c := by
      simp [abs_mul]
    rw [h3]
    field_simp [ha, hc, show a * c ≠ 0 by
      apply mul_ne_zero
      exact ha
      exact hc
    ]

  have h3 : a * d / abs (a * d) = (a / abs a) * (d / abs d) := by
    have h4 : abs (a * d) = abs a * abs d := by
      simp [abs_mul]
    rw [h4]
    field_simp [ha, hd, show a * d ≠ 0 by
      apply mul_ne_zero
      exact ha
      exact hd
    ]

  have h4 : b * c / abs (b * c) = (b / abs b) * (c / abs c) := by
    have h5 : abs (b * c) = abs b * abs c := by
      simp [abs_mul]
    rw [h5]
    field_simp [hb, hc, show b * c ≠ 0 by
      apply mul_ne_zero
      exact hb
      exact hc
    ]

  have h5 : b * d / abs (b * d) = (b / abs b) * (d / abs d) := by
    have h6 : abs (b * d) = abs b * abs d := by
      simp [abs_mul]
    rw [h6]
    field_simp [hb, hd, show b * d ≠ 0 by
      apply mul_ne_zero
      exact hb
      exact hd
    ]

  have h6 : c * d / abs (c * d) = (c / abs c) * (d / abs d) := by
    have h7 : abs (c * d) = abs c * abs d := by
      simp [abs_mul]
    rw [h7]
    field_simp [hc, hd, show c * d ≠ 0 by
      apply mul_ne_zero
      exact hc
      exact hd
    ]

  have h7 : a * b * c / abs (a * b * c) = (a / abs a) * (b / abs b) * (c / abs c) := by
    have h8 : abs (a * b * c) = abs a * abs b * abs c := by
      simp [abs_mul]
    rw [h8]
    field_simp [ha, hb, hc, show a * b * c ≠ 0 by
      apply mul_ne_zero
      apply mul_ne_zero
      exact ha
      exact hb
      exact hc
    ]

  have h8 : a * b * d / abs (a * b * d) = (a / abs a) * (b / abs b) * (d / abs d) := by
    have h9 : abs (a * b * d) = abs a * abs b * abs d := by
      simp [abs_mul]
    rw [h9]
    field_simp [ha, hb, hd, show a * b * d ≠ 0 by
      apply mul_ne_zero
      apply mul_ne_zero
      exact ha
      exact hb
      exact hd
    ]

  have h9 : a * c * d / abs (a * c * d) = (a / abs a) * (c / abs c) * (d / abs d) := by
    have h10 : abs (a * c * d) = abs a * abs c * abs d := by
      simp [abs_mul]
    rw [h10]
    field_simp [ha, hc, hd, show a * c * d ≠ 0 by
      apply mul_ne_zero
      apply mul_ne_zero
      exact ha
      exact hc
      exact hd
    ]

  have h10 : b * c * d / abs (b * c * d) = (b / abs b) * (c / abs c) * (d / abs d) := by
    have h11 : abs (b * c * d) = abs b * abs c * abs d := by
      simp [abs_mul]
    rw [h11]
    field_simp [hb, hc, hd, show b * c * d ≠ 0 by
      apply mul_ne_zero
      apply mul_ne_zero
      exact hb
      exact hc
      exact hd
    ]

  have h11 : a * b * c * d / abs (a * b * c * d) = (a / abs a) * (b / abs b) * (c / abs c) * (d / abs d) := by
    have h12 : abs (a * b * c * d) = abs a * abs b * abs c * abs d := by
      simp [abs_mul]
    rw [h12]
    field_simp [ha, hb, hc, hd, show a * b * c * d ≠ 0 by
      apply mul_ne_zero
      apply mul_ne_zero
      apply mul_ne_zero
      exact ha
      exact hb
      exact hc
      exact hd
    ]

  rcases ha1 with ha1 | ha1 <;> rcases hb1 with hb1 | hb1 <;> rcases hc1 with hc1 | hc1 <;> rcases hd1 with hd1 | hd1 <;> 
    norm_num [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ha1, hb1, hc1, hd1]