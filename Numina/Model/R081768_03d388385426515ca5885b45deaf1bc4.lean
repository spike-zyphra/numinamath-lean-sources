import Mathlib

theorem algebra_281561 (M m D d : ℝ)
    (hM : M ≠ 0) (hm : m ≠ 0) (hD : D ≠ 0) (hd : d ≠ 0)
    (h1 : (2 * M + m + D + d) / (M + m + D + d) = 1.05)
    (h2 : (M + 2 * m + D + d) / (M + m + D + d) = 1.15)
    (h3 : (M + m + 2 * D + d) / (M + m + D + d) = 1.25) :
    (M + m + D + 2 * d) / (M + m + D + d) = 1.55 := by
  have hT1 : M + m + D + d ≠ 0 := by
    by_contra h
    rw [h] at h1 h2 h3
    norm_num at h1 h2 h3
  have eq1 : 2 * M + m + D + d = 1.05 * (M + m + D + d) := by
    field_simp [hT1] at h1
    linarith
  have eq2 : M + 2 * m + D + d = 1.15 * (M + m + D + d) := by
    field_simp [hT1] at h2
    linarith
  have eq3 : M + m + 2 * D + d = 1.25 * (M + m + D + d) := by
    field_simp [hT1] at h3
    linarith
  have h4 : m = 3 * M := by
    ring_nf at eq1 eq2 eq3
    nlinarith
  have h5 : D = 5 * M := by
    ring_nf at eq1 eq2 eq3
    nlinarith [h4]
  have h6 : d = 11 * M := by
    ring_nf at eq1 eq2 eq3
    nlinarith [h4, h5]
  have hT : M + m + D + d = 20 * M := by
    linarith [h4, h5, h6]
  have : M + m + D + 2 * d = 31 * M := by
    linarith [h4, h5, h6]
  field_simp [hT1]
  nlinarith