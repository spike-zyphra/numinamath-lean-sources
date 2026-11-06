import Mathlib

theorem algebra_140088 (x y : ℤ) (hx : x > 0) (hy : y > 0)
    (h : 2 * x ^ 2 + 5 * y ^ 2 = 11 * (x * y - 11)) :
    (x, y) = (14, 27) := by
  have h1 : 2 * x ^ 2 + 5 * y ^ 2 = 11 * (x * y - 11) := h
  have h2 : (2 * x - y) * (x - 5 * y) = -121 := by
    linarith
  have h4 : (2 * x - y) ∣ -121 := by 
    use (x - 5 * y)
    all_goals linarith
  have h13 : (2 * x - y) ∣ 121 := by
    have h6 : (2 * x - y) ∣ -121 := h4
    have h7 : (2 * x - y) ∣ 121 := by
      exact Int.dvd_neg.mp h6
    exact h7
  have h14 : (2 * x - y) = 1 ∨ (2 * x - y) = -1 ∨ (2 * x - y) = 11 ∨ (2 * x - y) = -11 ∨ (2 * x - y) = 121 ∨ (2 * x - y) = -121 := by 
    have h15 : (2 * x - y) ∣ 121 := h13
    have h16 : (2 * x - y) ≤ 121 := by 
      apply Int.le_of_dvd (by norm_num) h15
    have h17 : (2 * x - y) ≥ -121 := by
      have h18 : - (2 * x - y) ∣ 121 := by 
        exact Int.neg_dvd.2 h15
      have h19 : - (2 * x - y) ≤ 121 := by
        apply Int.le_of_dvd (by norm_num) h18
      omega
    interval_cases k : (2 * x - y) <;> try { tauto }
  rcases h14 with (h15 | h15 | h15 | h15 | h15 | h15)
  · -- case 1
    have h16 : (x - 5 * y) = -121 := by
      rw [h15] at h2
      linarith
    have hx1 : x = 14 := by 
      omega
    have hy1 : y = 27 := by 
      omega
    simp [Prod.ext_iff, hx1, hy1]
  · -- case 2
    have h16 : (x - 5 * y) = 121 := by
      rw [h15] at h2
      linarith
    omega
  · -- case 3
    have h16 : (x - 5 * y) = -11 := by
      rw [h15] at h2
      linarith
    omega
  · -- case 4
    have h16 : (x - 5 * y) = 11 := by
      rw [h15] at h2
      linarith
    omega
  · -- case 5
    have h16 : (x - 5 * y) = -1 := by
      rw [h15] at h2
      linarith
    omega
  · -- case 6
    have h16 : (x - 5 * y) = 1 := by
      rw [h15] at h2
      linarith
    omega