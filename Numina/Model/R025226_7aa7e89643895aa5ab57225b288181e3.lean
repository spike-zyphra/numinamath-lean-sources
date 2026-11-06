import Mathlib

theorem number_theory_1733
    (x y z : ℤ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (h : 11 ∣ 7 * x + 2 * y - 5 * z) :
    11 ∣ 3 * x + 4 * y + 12 * z := by
  have h1 : 11 ∣ 2 * (7 * x + 2 * y - 5 * z) := by
    exact dvd_mul_of_dvd_right h 2
  have h2 : 11 ∣ (3 * x + 4 * y + 12 * z - (2 * (7 * x + 2 * y - 5 * z))) := by
    have h3 : (3 * x + 4 * y + 12 * z - (2 * (7 * x + 2 * y - 5 * z)))
          = 11 * (-x + 2 * z) := by
      ring
    rw [h3] 
    use (-x + 2 * z)
    all_goals ring
  have h3 : 11 ∣ 3 * x + 4 * y + 12 * z := by
    have h4 : 11 ∣ (3 * x + 4 * y + 12 * z) := by
      have eq1 : 3 * x + 4 * y + 12 * z = 2 * (7 * x + 2 * y - 5 * z) + (3 * x + 4 * y + 12 * z - (2 * (7 * x + 2 * y - 5 * z))) := by
        ring
      rw [eq1] 
      apply dvd_add 
      exact h1 
      exact h2 
    exact h4
  exact h3