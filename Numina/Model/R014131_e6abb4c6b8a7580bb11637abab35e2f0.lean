import Mathlib

theorem algebra_4134 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : 6 * x + 6 * y = 11) (h2 : 8 * x + 8 * z = 13) (h3 : 12 * y + 12 * z = 9)
    (n m : ℕ) (hn : n > 0) (hm : m > 0) (hnm : m = n * x + n * y + n * z) :
    m ≥ 101 := by

  have h4 : x + y = (11 / 6 : ℝ) := by
    have eq1 : 6 * x + 6 * y = (11 : ℝ) := by linarith
    linarith

  have h5 : x + z = (13 / 8 : ℝ) := by
    have eq2 : 8 * x + 8 * z = (13 : ℝ) := by linarith
    linarith

  have h6 : y + z = (3 / 4 : ℝ) := by
    have eq3 : 12 * y + 12 * z = (9 : ℝ) := by linarith
    linarith

  have h7 : x + y + z = (101 / 48 : ℝ) := by
    linarith [h4, h5, h6]

  have eq4 : (m : ℝ) = (n : ℝ) * (x + y + z) := by
    have eq5 : (m : ℝ) = (n : ℝ) * x + (n : ℝ) * y + (n : ℝ) * z := by
      exact_mod_cast hnm
    have eq6 : (n : ℝ) * x + (n : ℝ) * y + (n : ℝ) * z = (n : ℝ) * (x + y + z) := by ring
    rw [eq6] at eq5
    linarith

  rw [show x + y + z = (101 / 48 : ℝ) by linarith [h7] ] at eq4
  have h8 : (m : ℝ) = (n : ℝ) * (101 / 48) := eq4

  by_contra h
  push_neg at h
  have hm_eq : m < 101 := h

  have eq5 : (48 * (m : ℝ) = 101 * (n : ℝ)) := by
    have eq6 : (m : ℝ) = (n : ℝ) * (101 / 48) := h8
    field_simp at eq6 ⊢
    linarith

  have eq8 : 48 * m = 101 * n := by
    have eq7 : (48 * (m : ℝ) = 101 * (n : ℝ)) := eq5
    exact_mod_cast eq7

  omega