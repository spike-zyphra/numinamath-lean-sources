import Mathlib

theorem algebra_312908 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (hd : d > 0) (h1 : (2 * a + b + c + d) / (a + b + c + d) = 1.05) (h2 : (a + 2 * b + c + d) / (a + b + c + d) = 1.15)
    (h3 : (a + b + 2 * c + d) / (a + b + c + d) = 1.25) :
    (a + b + c + 2 * d) / (a + b + c + d) = 1.55 := by

  have h4 : a + b + c + d ≠ 0 := by positivity

  have eq1 : 2 * a + b + c + d = 1.05 * (a + b + c + d) := by 
    have h5 : a + b + c + d ≠ 0 := h4
    field_simp [h5] at h1
    linarith
  
  have eq2 : a + 2 * b + c + d = 1.15 * (a + b + c + d) := by 
    have h5 : a + b + c + d ≠ 0 := h4
    field_simp [h5] at h2
    linarith

  have eq3 : a + b + 2 * c + d = 1.25 * (a + b + c + d) := by 
    have h5 : a + b + c + d ≠ 0 := h4
    field_simp [h5] at h3
    linarith
  
  have eq4 : a + b + c + d = 20 * a := by
    nlinarith
  
  have eq5 : b = 3 * a := by
    nlinarith [eq1, eq2, eq3, eq4]

  have eq6 : c = 5 * a := by
    nlinarith [eq1, eq2, eq3, eq4]

  have eq7 : d = 11 * a := by
    nlinarith [eq1, eq2, eq3, eq4]

  have eq8 : a + b + c + d = 20 * a := by
    nlinarith
  
  have eq9 : a + b + c + 2 * d = 31 * a := by
    nlinarith [eq5, eq6, eq7]

  have eq10 : (a + b + c + 2 * d) / (a + b + c + d) = 1.55 := by 
    rw [eq9, eq8]
    have ha' : a ≠ 0 := by nlinarith
    field_simp [show (20 * a) ≠ 0 by
      intro h
      apply ha'
      nlinarith
    ]
    <;> ring_nf <;> nlinarith
  
  linarith [eq10]