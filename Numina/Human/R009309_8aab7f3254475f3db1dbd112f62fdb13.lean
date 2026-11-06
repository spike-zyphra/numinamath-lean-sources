import Mathlib

/- The perimeter of a rectangle is 56 meters. The ratio of its length to its width is 4:3. What is the length in meters of a diagonal of the rectangle? -/
theorem algebra_16650 {l w : ℝ} (hl : l > 0) (hw : w > 0)
    (hperim : 2 * (l + w) = 56) (hrat : l / w = 4 / 3) :
    Real.sqrt (l^2 + w^2) = 20 := by
  have h₀ : l = 4 / 3 * w := by
    apply Eq.symm
    field_simp at hrat
    linarith
  subst h₀
  ring_nf at hperim ⊢
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num <;> nlinarith