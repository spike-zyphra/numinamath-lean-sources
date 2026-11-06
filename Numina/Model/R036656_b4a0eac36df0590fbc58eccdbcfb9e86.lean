import Mathlib

theorem algebra_100939 (x y : ℤ) (h : 15 * x * y - 35 * x - 6 * y = 3) :
    (x, y) = (-3, 2) := by
  have h1 : (5 * x - 2) * (3 * y - 7) = 17 := by
    nlinarith
  have h2 : (5 * x - 2) * (3 * y - 7) = 17 := h1
  have h3 : (5 * x - 2) ∣ 17 := by
    use (3 * y - 7)
    all_goals linarith
  have h4 : (5 * x - 2) = 1 ∨ (5 * x - 2) = 17 ∨ (5 * x - 2) = -1 ∨ (5 * x - 2) = -17 := by
    have h5 : (5 * x - 2) ∣ 17 := h3
    have h6 : (5 * x - 2) ≤ 17 := by
      apply Int.le_of_dvd (by norm_num) h5
    have h7 : (5 * x - 2) ≥ -17 := by
      have h8 : (- (5 * x - 2)) ∣ 17 := by
        exact Int.neg_dvd.2 h5
      have h9 : - (5 * x - 2) ≤ 17 := by
        apply Int.le_of_dvd (by norm_num) h8
      omega
    interval_cases h : (5 * x - 2) <;> tauto
  rcases h4 with h4 | h4 | h4 | h4
  · -- Case1: 5 *x - 2 =1
    have h5 : (3 * y - 7) = 17 := by
      rw [h4] at h1
      linarith
    exfalso
    omega
  · -- Case2:5 *x - 2=17
    have h5 : (3 * y - 7) = 1 := by
      rw [h4] at h1
      linarith
    exfalso
    omega
  · -- Case3:5 *x - 2 = -1
    have h5 : (3 * y - 7) = -17 := by
      rw [h4] at h1
      linarith
    exfalso
    omega
  · -- Case4:5 *x - 2 = -17
    have h5 : (3 * y - 7) = -1 := by
      rw [h4] at h1
      linarith
    have hx : x = -3 := by
      omega
    have hy : y = 2 := by
      omega
    simp [Prod.ext_iff, hx, hy]