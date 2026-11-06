import Mathlib

theorem algebra_305307 {a b c : ℝ} (h : a * b * c = 1) :
    1 / (a + a * b + 1) + 1 / (b + b * c + 1) + 1 / (c + c * a + 1) =
    a / (a + a * b + 1) + b / (b + b * c + 1) + c / (c + c * a + 1) := by
  have eq1 : 1 / (a + a * b + 1) = c / (c + c * a + 1) := by
    have h1 : a + a * b + 1 = (c + c * a + 1) / c := by 
      field_simp [(show c ≠ 0 from by
        by_contra hc
        have hc' : c = 0 := by linarith
        rw [hc'] at h
        nlinarith
      )
      ]
      nlinarith [h]
    rw [h1]
    <;> field_simp [(show c ≠ 0 from by
      by_contra hc
      have hc' : c = 0 := by linarith
      rw [hc'] at h
      nlinarith
    )
    ]
    <;> nlinarith
  have eq2 : 1 / (b + b * c + 1) = a / (a + a * b + 1) := by
    have h2 : b + b * c + 1 = (a + a * b + 1) / a := by
      field_simp [(show a ≠ 0 from by
        by_contra ha
        have ha' : a = 0 := by linarith
        rw [ha'] at h
        nlinarith
      )
      ]
      nlinarith [h]
    rw [h2]
    <;> field_simp [(show a ≠ 0 from by
        by_contra ha
        have ha' : a = 0 := by linarith
        rw [ha'] at h
        nlinarith
      )
    ]
    <;> nlinarith
  have eq3 : 1 / (c + c * a + 1) = b / (b + b * c + 1) := by
    have h3 : c + c * a + 1 = (b + b * c + 1) / b := by
      field_simp [(show b ≠ 0 from by
        by_contra hb
        have hb' : b = 0 := by linarith
        rw [hb'] at h
        nlinarith
      )
      ]
      nlinarith [h]
    rw [h3]
    <;> field_simp [(show b ≠ 0 from by
        by_contra hb
        have hb' : b = 0 := by linarith
        rw [hb'] at h
        nlinarith
      )
    ]
    <;> nlinarith
  linarith [eq1, eq2, eq3]