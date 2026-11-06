import Mathlib

theorem algebra_322118 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x * y = 1) (p : ℝ) (hp : 0 < p) :
    (x * (1 + p / 100)) * y * (1 - q / 100) = 1 ↔
    q = 100 * p / (100 + p) := by
  constructor
  · -- Assume l.h.s. prove r.h.s.
    intro h
    have h_eq1 : (x * (1 + p / 100)) * y * (1 - q / 100) = 1 := by
      linarith
    have h_eq2 : (x * y) * (1 + p / 100) * (1 - q / 100) = 1 := by
      ring_nf at h_eq1 ⊢
      linarith
    rw [hxy] at h_eq2
    have h_eq3 : (1 + p / 100) * (1 - q / 100) = 1 := by
      nlinarith
    have h_eq4 : (1 + p / 100) * (1 - q / 100) = 1 := h_eq3
    have h_eq5 : (1 + p / 100) ≠ 0 := by
      positivity
    have h_eq6 : 1 - q / 100 = 1 / ((1 + p / 100) : ℝ) := by
      field_simp [h_eq5] at h_eq4 ⊢
      nlinarith
    have h_eq7 : q / 100 = 1 - (1 / ((1 + p / 100) : ℝ)) := by
      linarith [h_eq6]
    have h_eq8 : q / 100 = (p / 100) / ((1 + p / 100) : ℝ) := by
      rw [h_eq7]
      have h_eq5 : (1 + p / 100) ≠ 0 := by
        positivity
      field_simp [h_eq5]
      <;> ring_nf
    have h_eq9 : q = p / (1 + p / 100) := by
      have h_eq10 : q = (q / 100) * 100 := by
        ring_nf
      rw [h_eq10]
      rw [h_eq8]
      field_simp [h_eq5]
      <;> ring_nf
    have h_eq10 : q = 100 * p / (100 + p) := by
      rw [h_eq9]
      field_simp
      <;> ring_nf
    linarith [h_eq10]
  · -- Assume r.h.s. prove l.h.s.
    intro h_eq
    have h_eq1 : q = 100 * p / (100 + p) := by linarith
    have h_eq3 : (x * (1 + p / 100)) * y * (1 - q / 100) = 1 := by
      calc
        (x * (1 + p / 100)) * y * (1 - q / 100) = (x * y) * (1 + p / 100) * (1 - q / 100) := by ring_nf
        _ = (1) * (1 + p / 100) * (1 - q / 100) := by rw [hxy]
        _ = 1 := by
          rw [show q = 100 * p / (100 + p) by linarith [h_eq1]]
          field_simp
          <;> ring_nf
          <;> norm_num
          <;> nlinarith
    linarith [h_eq3]