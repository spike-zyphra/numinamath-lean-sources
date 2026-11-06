import Mathlib

theorem algebra_12837 {a : ℝ} (ha : a ≠ -1) (h : ∀ x, (x - a) / (x - a - 1) = 3 - (-1) * (x + 1)) :
    a = 2 := by

  have h1 := h (a + 1)
  have h2 := h (a + 2)

  have eq1 : (a + 1 - a) / (a + 1 - a - 1) = 3 - (-1) * ((a + 1) + 1) := by
    simpa using h1

  have eq2 : (a + 2 - a) / (a + 2 - a - 1) = 3 - (-1) * ((a + 2) + 1) := by
    simpa using h2

  have eq1' : (a + 1 - a) / (a + 1 - a - 1) = 0 := by
    have hx : a + 1 - a - 1 = (0 : ℝ) := by
      ring
    rw [hx]
    norm_num

  have eq2' : (a + 2 - a) / (a + 2 - a - 1) = 2 := by
    have hx : a + 2 - a - 1 = (1 : ℝ) := by
      ring
    have hy : a + 2 - a = (2 : ℝ) := by
      ring
    rw [hx]
    norm_num [hy]

  have h1' : 0 = a + 5 := by
    norm_num [eq1'] at eq1
    linarith

  have h2' : 2 = a + 6 := by
    rw [eq2'] at eq2
    ring_nf at eq2 ⊢
    linarith [eq2]

  linarith [h1', h2']