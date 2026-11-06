import Mathlib

theorem algebra_197455 {x y z : ℝ} (hxy : x ≠ -y) (hzz : y ≠ -z) (hzz' : x ≠ -z)
    (h1 : 1 / (x + y) + 1 / (x + z) = 7 / 12) (h2 : 1 / (x + y) + 1 / (y + z) = 8 / 15)
    (h3 : 1 / (x + z) + 1 / (y + z) = 9 / 20) :
    (x, y, z) = (1, 2, 3) := by

  have h4 : x + y ≠ 0 := by
    intro h
    apply hxy
    linarith

  have h5 : y + z ≠ 0 := by
    intro h
    apply hzz
    linarith

  have h6 : x + z ≠ 0 := by
    intro h
    apply hzz'
    linarith

  have eq5 : 1 / (x + y) - 1 / (y + z) = 2 / 15 := by
    have eq4 : (1 / (x + y) + 1 / (x + z)) - (1 / (x + z) + 1 / (y + z) ) = 7 / 12 - 9 / 20 := by
      linarith [h1, h3]
    have eq6 : (1 / (x + y) + 1 / (x + z)) - (1 / (x + z) + 1 / (y + z)) = 1 / (x + y) - 1 / (y + z) := by
      ring
    rw [eq6] at eq4
    norm_num at eq4 ⊢
    linarith

  have eq7 : 1 / (x + y) = 1 / 3 := by
    have eq8 : 1 / (x + y) - 1 / (y + z) = 2 / 15 := eq5
    have eq9 : 1 / (x + y) + 1 / (y + z) = 8 / 15 := by linarith [h2]
    have eq10 : 2 * (1 / (x + y)) = 2 / 3 := by
      linarith
    linarith

  have eq8 : x + y = 3 := by
    field_simp [h4] at eq7
    all_goals linarith

  have eq9 : 1 / (x + z) = 1 / 4 := by
    have eq11 : 1 / (x + y) + 1 / (x + z) = 7 / 12 := by linarith [h1]
    rw [show 1 / (x + y) = 1 / 3 by linarith [eq7]] at eq11
    linarith

  have eq10 : x + z = 4 := by
    field_simp [h6] at eq9
    all_goals linarith

  have eq11 : 1 / (y + z) = 1 / 5 := by
    have eq13 : 1 / (x + z) + 1 / (y + z) = 9 / 20 := by linarith [h3]
    rw [show 1 / (x + z) = 1 / 4 by linarith [eq9]] at eq13
    linarith

  have eq12 : y + z = 5 := by
    field_simp [h5] at eq11
    all_goals linarith

  have hx1 : x = 1 := by
    linarith [eq8, eq10, eq12]

  have hy1 : y = 2 := by
    linarith [eq8, eq10, eq12]

  have hz1 : z = 3 := by
    linarith [eq8, eq10, eq12]

  simp [hx1, hy1, hz1]