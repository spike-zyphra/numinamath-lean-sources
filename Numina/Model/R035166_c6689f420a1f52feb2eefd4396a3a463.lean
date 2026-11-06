import Mathlib
open Set

theorem algebra_9178 : image (fun (x : ℝ) => x^2 - 2*x) (Icc 0 3) = {x | -1 ≤ x ∧ x ≤ 3} := by
  ext y
  simp only [mem_image, mem_setOf_eq, mem_Icc]
  constructor
  · -- If y is in the image, then y is in [-1, 3]
    rintro ⟨x, hx, rfl⟩
    have h0 : 0 ≤ x := by linarith [hx.1]
    have h1 : x ≤ 3 := by linarith [hx.2]
    constructor
    · -- Show that -1 ≤ x^2 - 2*x
      nlinarith [sq_nonneg (x - 1)]
    · -- Show that x^2 - 2*x ≤ 3
      nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 0)]
  · -- Show the reverse direction: if y in [-1, 3], then in image
    rintro ⟨hy1, hy2⟩
    use 1 + Real.sqrt (1 + y)
    constructor
    · -- Show that 0 ≤ 1 + Real.sqrt (1 + y) ≤ 3
      constructor
      · -- 0 ≤ 1 + Real.sqrt (1 + y)
        nlinarith [Real.sqrt_nonneg (1 + y)]
      · -- 1 + Real.sqrt (1 + y) ≤ 3
        nlinarith [Real.sqrt_nonneg (1 + y), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + y by linarith)]
    · -- Show that (1 + Real.sqrt (1 + y))^2 - 2*(1 + Real.sqrt (1 + y)) = y
      nlinarith [Real.sqrt_nonneg (1 + y), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + y by linarith)]