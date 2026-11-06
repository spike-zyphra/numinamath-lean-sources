import Mathlib

theorem number_theory_108882 (x y : ℤ) (hx : x > 0) (hy : y > 0) (h : x * (x - y) = 8 * y - 7) :
    (x, y) = (63, 56) := by
  have h1 : x ^ 2 + 7 = y * (x + 8) := by 
    linarith

  have h2 : x + 8 ∣ x ^ 2 + 7 := by
    use y
    linarith

  have h3 : x + 8 ∣ 71 := by
    have h4 : x + 8 ∣ x ^ 2 + 7 := h2
    have h5 : x + 8 ∣ (x + 8) * (x - 8) := by
      apply dvd_mul_right
    have h6 : x + 8 ∣ ((x ^ 2 + 7) - (x + 8) * (x - 8)) := by 
      apply Dvd.dvd.sub
      · exact h4
      · exact h5
    have h7 : (x ^ 2 + 7) - (x + 8) * (x - 8) = 71 := by
      nlinarith
    rw [h7] at h6
    exact h6
  
  have h5 : x + 8 = 1 ∨ x + 8 = -1 ∨ x + 8 = 71 ∨ x + 8 = -71 := by
    have h6 : x + 8 ∣ 71 := h3
    have h7 : x + 8 ≤ 71 := by 
      apply Int.le_of_dvd (by norm_num) h6 
    have h8 : x + 8 ≥ -71 := by 
      have h9 : - (x + 8) ∣ 71 := by 
        exact Int.neg_dvd.2 h6 
      have h10 : - (x + 8) ≤ 71 := by
        apply Int.le_of_dvd (by norm_num) h9 
      omega
    interval_cases h9 : x + 8 <;> tauto
  
  rcases h5 with h6 | h7 | h8 | h9
  
  · -- Case x + 8 = 1, so x = -7 which is a contradiction
    have h10 : x = -7 := by 
      linarith 
    linarith

  · -- Case x + 8 = -1, so x = -9 which is a contradiction
    have h11 : x = -9 := by 
      linarith 
    linarith

  · -- Case x + 8 = 71, so x = 63
    have h12 : x = 63 := by
      linarith
    have h13 : y = 56 := by 
      rw [h12] at h1
      linarith
    simp [Prod.ext_iff, h12, h13]

  · -- Case x + 8 = -71, so x = -79 which is a contradiction
    have h14 : x = -79 := by 
      linarith 
    linarith