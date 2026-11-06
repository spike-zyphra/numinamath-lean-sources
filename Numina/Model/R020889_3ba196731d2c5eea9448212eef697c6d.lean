import Mathlib

open Real Set

/- Let $x$, $y$ be positive real numbers, and $x+y=1$, then the minimum value of $\frac{x^2}{x+2}+\frac{y^2}{y+1}$ is ___          ___. -/
theorem algebra_11474 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) :
    IsLeast {z | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ x + y = 1 ∧ z = x ^ 2 / (x + 2) + y ^ 2 / (y + 1)} (1 / 4) := by
  constructor
  · -- Show that 1/4 is in the set
    use 2 / 3, 1 / 3
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 1/4 is the least element in the set
    intro z hz
    rcases hz with ⟨x, y, hx, hy, hxy, hz⟩
    have h3 : y = 1 - x := by linarith
    rw [h3] at hz
    have h4 : 0 < 1 - x := by
      nlinarith [hxy, hx, hy]
    have h5 : x ^ 2 / (x + 2) + (1 - x) ^ 2 / ( (1 - x) + 1 ) ≥ 1 / 4 := by
      have h6 : 0 < x := hx
      have h8 : 0 < 1 - x := h4
      have h9 : 0 < x + 2 := by
        nlinarith
      have h10 : 0 < (1 - x) + 1 := by
        nlinarith
      have h11 : x ^ 2 / (x + 2) + (1 - x) ^ 2 / ( (1 - x) + 1 ) - 1 / 4 ≥ 0 := by
        have h10_pos : 0 < (1 - x) + 1 := by
          nlinarith
        have h9_pos : 0 < x + 2 := by
          nlinarith
        have pos1 : 0 < (x + 2) * ( (1 - x) + 1 ) * 4 := by
          positivity
        have h12 : x ^ 2 / (x + 2) + (1 - x) ^ 2 / ( (1 - x) + 1 ) - 1 / 4 =
            (4 * x ^ 2 * ( (1 - x) + 1 ) + 4 * (1 - x) ^ 2 * (x + 2) - (x + 2) * ( (1 - x) + 1 )) / ( (x + 2) * ( (1 - x) + 1 ) * 4 ) := by
          field_simp
          ring
        rw [h12]
        apply div_nonneg
        nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (x - 4 / 3), sq_nonneg (x * (x - 2 / 3)), sq_nonneg ((1 - x) * (x - 2 / 3)), mul_pos hx (show 0 < (1 - x) by nlinarith), mul_pos hx (show 0 < x + 2 by nlinarith), mul_pos (show 0 < (1 - x) by nlinarith) (show 0 < (1 - x) + 1 by nlinarith)]
        positivity
      linarith
    linarith [hz, h5]