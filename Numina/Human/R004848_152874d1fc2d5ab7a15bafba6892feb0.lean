import Mathlib

/- Find all real numbers $x, y, z$ so that

$$
\begin{aligned}
x^{2} y+y^{2} z+z^{2} & =0 \\
z^{3}+z^{2} y+z y^{3}+x^{2} y & =\frac{1}{4}\left(x^{4}+y^{4}\right)
\end{aligned}
$$ -/
theorem algebra_604214 :
    {(x, y, z) : ℝ × ℝ × ℝ | x ^ 2 * y + y ^ 2 * z + z ^ 2 = 0 ∧ z ^ 3 + z ^ 2 * y + z * y ^ 3 + x ^ 2 * y = 1 / 4 * (x ^ 4 + y ^ 4)} = {(0, 0, 0)} := by
  -- Break the goal into two parts.
  ext ⟨x, y, z⟩
  simp [-one_div]
  apply Iff.intro
  . rintro ⟨h₀, h₁⟩
    by_cases hy : y = 0
    . -- If y = 0, then x = y = z = 0.
      simp [hy] at h₀ h₁
      simp [h₀] at h₁
      tauto
    . -- Now assume that y ≠ 0.
      -- Show that z ≠ 0.
      have hz : z ≠ 0 := by
        by_contra! hz
        simp [hz] at h₀ h₁
        simp [hy] at h₀
        rw [h₀] at h₁
        -- Contradiction to y ≠ 0.
        simp [hy] at h₁
      -- Consider the discriminant of quadratic equation of x²y + y²z + z² = 0 w.r.t. to x, y and z repsectively.
      -- We have -y³z - yz² ≥ 0.
      have h₂ : -y ^ 3 * z - y * z ^ 2 ≥ 0 := by
        replace h₀ : (x * y) ^ 2 = -y ^ 3 * z - y * z ^ 2 := by
          rw [<-@mul_left_inj' _ _ _ _ y] at h₀
          linarith only [h₀]
          apply hy
        linarith only [h₀, sq_nonneg (x * y)]
      -- We have y⁴ - 4z³ ≥ 0.
      have h₃ : x ^ 4 - 4 * z ^ 3 ≥ 0 := by
        replace h₀ : (2 * y * z + x ^ 2) ^ 2 = x ^ 4 - 4 * z ^ 3 := by
          rw [<-@mul_left_inj' _ _ _ _ z] at h₀
          linarith only [h₀]
          apply hz
        linarith only [h₀, sq_nonneg (2 * y * z + x ^ 2)]
      -- We have y⁴ - 4x²y ≥ 0.
      have h₄ : y ^ 4 - 4 * x ^ 2 * y ≥ 0 := by
        replace h₀ : (2 * z + y ^ 2) ^ 2 = y ^ 4 - 4 * x ^ 2 * y := by
          linarith only [h₀]
        linarith only [h₀, sq_nonneg (2 * z + y ^ 2)]
      -- Note that the left-hand-side of h₂, h₃ and h₄ add up to 0, so they are all equal to 0.
      replace h₂ : -y ^ 3 * z - y * z ^ 2 = 0 := by
        linarith only [h₂, h₃, h₄, h₁]
      replace h₃ : x ^ 4 - 4 * z ^ 3 = 0 := by
        linarith only [h₂, h₃, h₄, h₁]
      replace h₄ : y ^ 4 - 4 * x ^ 2 * y = 0 := by
        linarith only [h₂, h₃, h₄, h₁]
      -- The three equations are contrary to the assumptions that y, z ≠ 0.
      rw [show y ^ 4 = y ^ 3 * y by ring, <-sub_mul] at h₄
      -- Show that y³ = 4x².
      simp [hy] at h₄
      replace h₄ : x ^ 2 = y ^ 3 / 4 := by
        linarith only [h₄]
      -- Substitute this into h₃ to get y⁶ = 64z³.
      rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, h₄] at h₃
      field_simp at h₃
      ring_nf at h₃
      -- Show that y² = 4z.
      replace h₃ : (y ^ 2 - 4 * z) * ((y ^ 2 + 2 * z) ^ 2 + 12 * z ^ 2) = 0 := by
        linarith only [h₃]
      rw [mul_eq_zero_iff_right (by positivity)] at h₃
      replace h₃ : z = y ^ 2 / 4 := by
        linarith only [h₃]
      -- Substitute this into h₂ to get a relation only in y.
      rw [h₃] at h₂
      ring_nf at h₂
      simp at h₂
      -- We get y = 0, contradicting our assumption.
      contradiction
  . rintro ⟨hx, hy, hz⟩
    simp [hx, hy, hz]
