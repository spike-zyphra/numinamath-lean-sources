import Mathlib

open BigOperators Real Set

theorem algebra_599618 :
  IsLeast {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 1 ∧ t =
    (3 * x^2 - x) / (1 + x^2) + (3 * y^2 - y) / (1 + y^2) +
    (3 * z^2 - z) / (1 + z^2)} 0 := by
  constructor
  · -- Show that $0$ is in the set.
    use 1 / 3, 1 / 3, 1 / 3
    norm_num
  · -- Show that $0$ is the least element in the set.
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, heq⟩
    have h2 : (3 * x^2 - x) / (1 + x^2) + (3 * y^2 - y) / (1 + y^2) + (3 * z^2 - z) / (1 + z^2) ≥ 0 := by
      have h3 : (3 * x^2 - x) / (1 + x^2) + (3 * y^2 - y) / (1 + y^2) + (3 * z^2 - z) / (1 + z^2) =
          ( (3 * x^2 - x) * (1 + y^2) * (1 + z^2) + (3 * y^2 - y) * (1 + x^2) * (1 + z^2) + (3 * z^2 - z) * (1 + x^2) * (1 + y^2) ) / ( (1 + x^2) * (1 + y^2) * (1 + z^2) ) := by
        field_simp
        <;> ring
      rw [h3]
      have h4 : ( (3 * x^2 - x) * (1 + y^2) * (1 + z^2) + (3 * y^2 - y) * (1 + x^2) * (1 + z^2) + (3 * z^2 - z) * (1 + x^2) * (1 + y^2) ) ≥ 0 := by
        have h2 : z = 1 - x - y := by
          linarith
        rw [h2]
        nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg ((1 - x - y) - 1 / 3),
          sq_nonneg (x * y - 1 / 9), sq_nonneg (y * (1 - x - y) - 1 / 9), sq_nonneg (x * (1 - x - y) - 1 / 9),
          sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)),
          mul_pos hx hy, mul_pos hy (show 0 < 1 - x - y by nlinarith), mul_pos hx (show 0 < 1 - x - y by nlinarith)
        ]
      have h4_pos : (1 + x^2) * (1 + y^2) * (1 + z^2) > 0 := by
        positivity
      apply div_nonneg
      linarith
      all_goals
      positivity
    linarith