import Mathlib

theorem algebra_306943 : {r : ℝ | ∃x y, x + y = 1 ∧ x^4 + y^4 = 7 / 2 ∧ r = x^2 + y^2} = {2}:= by
  ext r
  simp
  constructor
  · rintro ⟨x, y, h₀, h₁, hr⟩
    have h2 : x^2 + y^2 = 1 - 2 * (x * y) := by
      have h00 : (x + y) ^ 2 = 1 := by
        rw [h₀]
        norm_num
      linarith [sq_nonneg (x - y)]
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), h₁, h2]
  · intro hr
    use (1 + √3) / 2
    use (1 - √3) / 2
    ring_nf
    rw [show 4 = 2 * 2 by norm_num, pow_mul, hr]
    field_simp [Real.sq_sqrt]
    norm_num
