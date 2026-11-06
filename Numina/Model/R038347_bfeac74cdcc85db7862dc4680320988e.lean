import Mathlib

theorem algebra_282518 :
  {(d1, d2, d3) : ℝ × ℝ × ℝ | d1 + d2 + d3 = 80 ∧ 
                             d1 / 21 + d2 / 12 + d3 / 30 = 47 / 12 ∧
                             d1 / 21 + d2 / 30 + d3 / 12 = 14 / 3} =
  {(35, 15, 30)} := by
  ext ⟨d1, d2, d3⟩
  simp
  constructor
  · -- First direction: system implies individual values
    rintro ⟨h1, h2, h3⟩
    have eq1 : d1 + d2 + d3 = 80 := by linarith
    have eq2 : 360 * d1 + 630 * d2 + 252 * d3 = 29610 := by
      linarith [h2]
    have eq3 : 360 * d1 + 252 * d2 + 630 * d3 = 35280 := by
      linarith [h3]
    have eq4 : d3 = d2 + 15 := by
      linarith
    have eq5 : d1 = 65 - 2 * d2 := by
      linarith [eq1, eq4]
    have eq6 : d2 = 15 := by
      rw [eq5, eq4] at eq2
      linarith
    have eq7 : d3 = 30 := by
      linarith [eq4, eq6]
    have eq8 : d1 = 35 := by
      linarith [eq5, eq6]
    simp [eq8, eq6, eq7]
  · -- Show that (35, 15, 30) satisfy the system.
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num