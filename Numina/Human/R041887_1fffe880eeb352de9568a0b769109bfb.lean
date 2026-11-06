import Mathlib

open Real Set
open scoped BigOperators

/- Continue the sequence $x . y, z, w$ satisfying $x y+2 y z+z w \leqslant A\left(x^{2}+y^{2}+z^{2}+w^{2}\right)$, then the minimum value of the real number $A$ is -/
theorem inequalities_137019 :
  IsLeast {A : ℝ | ∀ x y z w, x * y + 2 * y * z + z * w ≤ A * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2)} ((1 + √2) / 2) := by
  -- first prove 0 < 1 + √2 has this'll be used several times
  have h_pos : 0 < 1 + √2 := by positivity
  constructor
    -- first prove (1 + √2)/2 belongs to set, first prove 2 variable am-gm inequality
  . have aux (a b : ℝ) : 2*a*b ≤ a^2 + b^2 := by linarith [show 0 ≤ (a-b)^2 by positivity]
    rintro x y z w
    -- use am-gm 3 times with x, y; y, z; z, x (multiplied by some sutiable factors)
    have h₁ := aux (√(1 + √2) * x) (1 / √(1 + √2) * y)
    convert_to 2 * x * y ≤ (1 + √2) * x^2 + 1 / (1 + √2) * y^2 at h₁
    . field_simp
      ring_nf
    . ring_nf
      simp [h_pos]
      rw [Real.sq_sqrt (by linarith)]
      field_simp
      ring_nf
      simp
    have h₂ := aux y z
    have h₃ := aux (1 / √(1 + √2) * z) (√(1 + √2) * w)
    convert_to 2 * z * w ≤ 1 / (1 + √2) * z^2 + (1 + √2) * w^2 at h₃
    . field_simp
      ring_nf
    . ring_nf
      simp [h_pos]
      rw [Real.sq_sqrt (by linarith)]
      field_simp
      ring_nf
    replace aux : 1 / (1 + √2) / 2 + 1 = (1 + √2) / 2 := by
      field_simp
      ring_nf
      simp
      ring_nf
    -- the 3 inequalities prove the target
    have h : x * y + 2 * y * z + z * w ≤  (1 + √2) / 2 * x^2 + (1 / (1 + √2) / 2 + 1) * y^2 + (1/ (1 + √2) / 2 + 1) * z^2 + (1 + √2) / 2 * w^2 := by
      linarith [h₁, h₂, h₃]
    rw [aux] at h
    linear_combination h
    -- to prove (1 + √2) / 2 ≤ A, use values 1, (1 + √2), (1 + √2), 1 for x, y, z, w
  . rintro A h
    replace h := h 1 (1 + √2) (1 + √2) 1
    ring_nf at h
    simp at h
    ring_nf at h
    rw [
      show 8 + √2 * 6 = (1 + √2) * (2 * √2 + 4) by ring_nf; simp; ring_nf,
      show √2 * A * 4 + A * 8 = 2 * A * (2 * √2 + 4) by ring
    ] at h
    have : 0 < 2 * √2 + 4 := by positivity
    simp [this] at h
    linarith