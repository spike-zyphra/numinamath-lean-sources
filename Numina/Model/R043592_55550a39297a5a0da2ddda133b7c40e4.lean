import Mathlib

theorem algebra_286585 {x y z : ℝ} (K : ℝ) (hK : K = (x + y + z)^5 - (-x + y + z)^5 - (x - y + z)^5 - (x + y - z)^5) :
    x ∣ K ∧ y ∣ K ∧ z ∣ K := by 
  constructor
  · -- Show that x divides K
    use ((x + y + z)^5 - (-x + y + z)^5 - (x - y + z)^5 - (x + y - z)^5) / x
    rw [hK]
    by_cases hx : x = 0
    · -- Subcase x = 0
      rw [hx]
      ring
    · 
      field_simp [hx]
  constructor
  · -- Show that y divides K
    use ((x + y + z)^5 - (-x + y + z)^5 - (x - y + z)^5 - (x + y - z)^5) / y
    rw [hK]
    by_cases hy : y = 0
    · -- Subcase y = 0
      rw [hy]
      ring
    · 
      field_simp [hy]
  · -- Show that z divides K
    use ((x + y + z)^5 - (-x + y + z)^5 - (x - y + z)^5 - (x + y - z)^5) / z
    rw [hK]
    by_cases hz : z = 0
    · -- Subcase z = 0
      rw [hz]
      ring
    · 
      field_simp [hz]