import Mathlib

theorem algebra_238932 {x y : ℝ} (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1)
    (h1 : (1 - x) * (1 - y) = 0.4) (h2 : (1 - x) * y = 0.2) (h3 : x * (1 - y) = 0.6) :
    (1 + x + y) / (1 + x + (1 - y)) = 6 := by
  have h4 : 0 ≤ x := by
    have hx1 : x ≥ 0 := by
      have h1' : x ∈ Set.Icc (0 : ℝ) 1 := hx
      exact h1'.1
    linarith
  have h5 : 0 ≤ y := by
    have hy1 : y ≥ 0 := by
      have h1' : y ∈ Set.Icc (0 : ℝ) 1 := hy
      exact h1'.1
    linarith
  have h6 : x ≤ 1 := by
    have hx1 : x ≤ 1 := by
      have h1' : x ∈ Set.Icc (0 : ℝ) 1 := hx
      exact h1'.2
    linarith
  have h7 : y ≤ 1 := by
    have hy1 : y ≤ 1 := by
      have h1' : y ∈ Set.Icc (0 : ℝ) 1 := hy
      exact h1'.2
    linarith
  have eq1 : x = 0.4 := by
    ring_nf at h1 h2
    nlinarith [sq_nonneg (x - 0.4), sq_nonneg (y - 1 / 3), h4, h6]
  have eq2 : y = (1 : ℝ) / 3 := by
    ring_nf at h1 h2
    rw [eq1] at h2
    nlinarith
  -- From eq1 and eq2, we can compute h3 and reach contradiction.
  have eq3 : x * (1 - y) = (4 / 15 : ℝ) := by
    rw [eq1, eq2]
    norm_num
  -- Computing h3's right side with eq1 and eq2.
  have eq4 : x * (1 - y) = (0.6 : ℝ) := by
    linarith [h3]
  -- Equating the two expressions for x * (1 - y) to reach contradiction.
  have eq5 : (0.6 : ℝ) = (4 / 15 : ℝ) := by
    linarith [eq3, eq4]
  norm_num at eq5
  all_goals
    linarith