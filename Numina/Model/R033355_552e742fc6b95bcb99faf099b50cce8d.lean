import Mathlib

theorem algebra_95005 {a r : ℚ} (hr : r ≠ 0) (h1 : a * (1 - r ^ 2011) / (1 - r) = 200)
(h2 : a * (1 - r ^ 4022) / (1 - r) = 380) :
a * (1 - r ^ 6033) / (1 - r) = 542 := by

  have hne : (1 - r) ≠ 0 := by
    by_contra h
    have : r = 1 := by linarith 
    rw [this] at h1 h2
    norm_num at h1 h2

  have eq1 : a * (1 - r ^ 2011) = 200 * (1 - r) := by
    have hne : (1 - r) ≠ 0 := hne
    field_simp [hne] at h1 
    linarith 
  have eq2 : a * (1 - r ^ 4022) = 380 * (1 - r) := by 
    have hne : (1 - r) ≠ 0 := hne
    field_simp [hne] at h2 
    linarith

  have eq3 : r ^ 2011 = 9 / 10 := by 
    have eq4 : a * (1 - r ^ 4022) = (a * (1 - r ^ 2011) ) * (1 + r ^ 2011) := by 
      ring_nf 
    rw [eq4] at eq2
    rw [show a * (1 - r ^ 2011) = 200 * (1 - r) by 
          nlinarith [eq1]
        ] at eq2
    apply (mul_left_inj' hne).mp
    linarith

  have eq4 : r ^ 4022 = 81 / 100 := by 
    calc 
      r ^ 4022 = (r ^ 2011) ^ 2 := by ring 
      _ = (9 / 10) ^ 2 := by rw [eq3] 
      _ = 81 / 100 := by norm_num

  have eq5 : a * (1 - r ^ 6033) = 542 * (1 - r) := by
    have eq6 : a * (1 - r  ^ 6033) = a * (1 - r ^ 2011) * (1 + r ^ 2011 + r ^ 4022) := by 
      ring_nf
    rw [eq6]
    rw [show a * (1 - r ^ 2011) = 200 * (1 - r) by 
          linarith [eq1]
        ]
    rw [show r ^ 4022 = 81 / 100 by 
          linarith [eq4]
        ]
    nlinarith [eq1, eq3, eq4]

  field_simp [hne] at *
  nlinarith [eq5]