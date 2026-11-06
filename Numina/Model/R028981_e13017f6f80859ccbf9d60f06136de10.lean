import Mathlib

open Finset Real

theorem algebra_251455 {x y : ℝ} (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x * y ≠ 1)
    (star : ℝ → ℝ → ℝ) (hstar : star = fun a b => (a + b - 2 * a * b) / (1 - a * b)) :
    star x y / (1 - star x y) = x / (1 - x) + y / (1 - y) := by

  have h1 : star x y = (x + y - 2 * x * y) / (1 - x * y) := by
    rw [hstar]

  rw [h1]

  have hx1 : 1 - x ≠ 0 := by
    intro h
    apply hx
    linarith

  have hy1 : 1 - y ≠ 0 := by
    intro h
    apply hy
    linarith

  have hx2 : 1 - x * y ≠ 0 := by
    intro h
    apply hxy
    linarith

  have h_eq : ((x + y - 2 * x * y) / (1 - x * y)) / (1 - ((x + y - 2 * x * y) / (1 - x * y))) = x / (1 - x) + y / (1 - y) := by

    have h_eq1 : 1 - ((x + y - 2 * x * y) / (1 - x * y)) = (1 - x - y + x * y) / (1 - x * y) := by
      field_simp [(show (1 - x * y) ≠ 0 by exact hx2)]
      ring

    rw [h_eq1]

    have h_eq2 : ((x + y - 2 * x * y) / (1 - x * y)) / ((1 - x - y + x * y) / (1 - x * y)) =
        (x + y - 2 * x * y) / (1 - x - y + x * y) := by 
      field_simp [(show (1 - x * y) ≠ 0 by exact hx2)]
      <;> ring

    rw [h_eq2]

    have hx_eq : 1 - x - y + x * y = (1 - x) * (1 - y) := by
      nlinarith

    rw [hx_eq]

    have eq2 : (x + y - 2 * x * y) / ((1 - x) * (1 - y)) = x / (1 - x) + y / (1 - y) := by 
      field_simp [(show (1 - x) ≠ 0 by exact hx1), (show (1 - y) ≠ 0 by exact hy1)]
      <;> ring

    linarith [eq2]

  linarith [h_eq]