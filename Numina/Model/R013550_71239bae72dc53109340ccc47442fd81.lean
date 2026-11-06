import Mathlib

theorem inequalities_110155 (a : Fin 5 → ℝ) (ha : ∀ i, a i > 1) :
    16 * (a 0 * a 1 * a 2 * a 3 * a 4 + 1) ≥
    (1 + a 0) * (1 + a 1) * (1 + a 2) * (1 + a 3) * (1 + a 4) := by
  have h1 : a 0 > 1 := ha 0
  have h2 : a 1 > 1 := ha 1
  have h3 : a 2 > 1 := ha 2
  have h4 : a 3 > 1 := ha 3
  have h5 : a 4 > 1 := ha 4
  nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2),
          mul_pos (sub_pos.mpr h1) (sub_pos.mpr h3),
          mul_pos (sub_pos.mpr h1) (sub_pos.mpr h4),
          mul_pos (sub_pos.mpr h1) (sub_pos.mpr h5),
          mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3),
          mul_pos (sub_pos.mpr h2) (sub_pos.mpr h4),
          mul_pos (sub_pos.mpr h2) (sub_pos.mpr h5),
          mul_pos (sub_pos.mpr h3) (sub_pos.mpr h4),
          mul_pos (sub_pos.mpr h3) (sub_pos.mpr h5),
          mul_pos (sub_pos.mpr h4) (sub_pos.mpr h5),
          mul_pos (mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2)) (mul_pos (sub_pos.mpr h3) (sub_pos.mpr h4)),
          mul_pos (mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2)) (sub_pos.mpr h5),
          mul_pos (mul_pos (sub_pos.mpr h1) (sub_pos.mpr h3)) (sub_pos.mpr h4),
          mul_pos (mul_pos (sub_pos.mpr h1) (sub_pos.mpr h3)) (sub_pos.mpr h5),
          mul_pos (mul_pos (sub_pos.mpr h1) (sub_pos.mpr h4)) (sub_pos.mpr h5),
          mul_pos (mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3)) (sub_pos.mpr h4),
          mul_pos (mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3)) (sub_pos.mpr h5),
          mul_pos (mul_pos (sub_pos.mpr h2) (sub_pos.mpr h4)) (sub_pos.mpr h5),
          mul_pos (mul_pos (sub_pos.mpr h3) (sub_pos.mpr h4)) (sub_pos.mpr h5)]