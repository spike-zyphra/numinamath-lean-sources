import Mathlib

theorem algebra_294398 (C : ℤ) (hC : ∃ a b c d, C = a * b ∧ C = c * d ∧ a - b = 5 ∧ c - d = 8) :
    C = 0 ∨ C = 84 := by
  rcases hC with ⟨a, b, c, d, h1, h2, h3, h4⟩
  have h5 : a = b + 5 := by
    omega
  have h6 : c = d + 8 := by
    omega
  rw [h5] at h1
  rw [h6] at h2
  have eq1 : (b + 5) * b = (d + 8) * d := by
    nlinarith [h1, h2]
  have eq2 : (2 * b + 5 : ℤ) ^ 2 = (2 * (d + 4) : ℤ) ^ 2 - 39 := by
    nlinarith
  have eq3 : ((2 * (d + 4) : ℤ) - (2 * b + 5 : ℤ)) * ((2 * (d + 4) : ℤ) + (2 * b + 5 : ℤ)) = 39 := by
    nlinarith [eq2]
  have h7 : ((2 * (d + 4) : ℤ) - (2 * b + 5 : ℤ)) ∣ 39 := by
    use ((2 * (d + 4) : ℤ) + (2 * b + 5 : ℤ))
    all_goals linarith [eq3]
  have h8 : ((2 * (d + 4) : ℤ) - (2 * b + 5 : ℤ)) ≤ 39 := by
    exact Int.le_of_dvd (by norm_num) h7
  have h9 : ((2 * (d + 4) : ℤ) - (2 * b + 5 : ℤ)) ≥ -39 := by
    have h10 : - ((2 * (d + 4) - (2 * b + 5) ) ) ∣ 39 := by
      exact Int.neg_dvd.2 h7
    have h11 : - ((2 * (d + 4) - (2 * b + 5) ) ) ≤ 39 := by
      exact Int.le_of_dvd (by norm_num) h10
    omega
  have h33 : (b = 7 ∨ b = 0 ∨ b = -12 ∨ b = -5) := by
    interval_cases h99 : ((2 * (d + 4) - (2 * b + 5) ) ) <;> try { 
      omega
    }
  rcases h33 with (r | r | r | r)
  · -- when b = 7
    have hb7 : b = 7 := by
      linarith
    rw [hb7] at h1
    have hc7 : C = 84 := by
      nlinarith
    right
    linarith
  · -- when b = 0
    have hb0 : b = 0 := by
      linarith
    rw [hb0] at h1
    have hc0 : C = 0 := by
      nlinarith
    left
    linarith
  · -- when b = -12
    have hb12 : b = -12 := by
      linarith
    rw [hb12] at h1
    have hc84 : C = 84 := by
      nlinarith
    right
    linarith
  · -- when b = -5
    have hb5 : b = -5 := by
      linarith
    rw [hb5] at h1
    have hc0 : C = 0 := by
      nlinarith
    left
    linarith