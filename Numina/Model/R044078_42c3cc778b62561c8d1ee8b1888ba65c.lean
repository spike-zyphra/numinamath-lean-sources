import Mathlib

theorem algebra_93853 (x y : ℝ) (hx : x ≠ -y) (h : (2 * x - y) / (x + y) = 2 / 3) :
    x / y = 5 / 4 := by
  have h1 : x + y ≠ 0 := by
    intro h2
    have : x = -y := by linarith
    contradiction

  have h2 : 3 * (2 * x - y) = 2 * (x + y) := by
    have h1' : x + y ≠ 0 := h1
    field_simp [h1'] at h ⊢
    linarith
  
  have h3 : 6 * x - 3 * y = 2 * x + 2 * y := by
    linarith [h2]

  have h4 : 4 * x = 5 * y := by
    linarith [h3]

  have hy : y ≠ 0 := by
    by_contra h5
    rw [h5] at h4
    have hx' : x = 0 := by linarith
    have h6 : x + y = 0 := by
      rw [hx', h5]
      norm_num
    contradiction
  
  have h5' : x / y = 5 / 4 := by
    have h6 : y ≠ 0 := hy
    field_simp [h6]
    linarith [h4]

  exact h5'