import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10596 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sin x ^ 4 - sin x * cos x + cos x ^ 4) :
  range f = {x | 0 ≤ x ∧ x ≤ 9 / 8} := by
  ext y
  simp [mem_range, mem_setOf_eq]
  constructor
  · -- First, show that if y ∈ range f, then 0 ≤ y ≤ 9/8
    rintro ⟨x, hx⟩
    have h1 : f x = sin x ^ 4 - sin x * cos x + cos x ^ 4 := h₀ x
    have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h3 : sin x ^ 4 + cos x ^ 4 = (sin x ^ 2 + cos x ^ 2) ^ 2 - 2 * (sin x * cos x) ^ 2 := by
      nlinarith 
    have h4 : sin x ^ 4 + cos x ^ 4 = 1 - 2 * (sin x * cos x) ^ 2 := by 
      rw [h3, h2]
      <;> nlinarith
    have h5 : -1 / 2 ≤ sin x * cos x ∧ sin x * cos x ≤ 1 / 2 := by
      have h6 : sin (2 * x) = 2 * sin x * cos x := by
        rw [show 2 * x = 2 * x by rfl]
        rw [sin_two_mul]
      have h7 : -1 ≤ sin (2 * x) ∧ sin (2 * x) ≤ 1 := by
        constructor
        · apply Real.neg_one_le_sin
        · apply Real.sin_le_one
      constructor
      · linarith [h6, h7.1]
      · linarith [h6, h7.2]
    have eq3 : f x = 1 - 2 * (sin x * cos x) ^ 2 - sin x * cos x := by
      have eq11 : f x = sin x ^ 4 - sin x * cos x + cos x ^ 4 := h₀ x
      have eq41 : sin x ^ 4 + cos x ^ 4 = 1 - 2 * (sin x * cos x) ^ 2 := h4
      nlinarith 
    have h14 : sin x * cos x ≥ -1 / 2 := by linarith [h5.left]
    have h15 : sin x * cos x ≤ 1 / 2 := by linarith [h5.right]
    have h16 : 0 ≤ 1 - 2 * (sin x * cos x) ^ 2 - sin x * cos x := by
      nlinarith [sq_nonneg (sin x * cos x + 1 / 4), sq_nonneg (sin x * cos x - 1 / 2), sq_nonneg (sin x * cos x + 1 / 2), 
        h14, h15, mul_nonneg (show 0 ≤ sin x * cos x + 1 / 2 by nlinarith) (show 0 ≤ 1 / 2 - sin x * cos x by nlinarith)]
    have h18 : 1 - 2 * (sin x * cos x) ^ 2 - sin x * cos x ≤ 9 / 8 := by
      nlinarith [sq_nonneg (sin x * cos x + 1 / 4), sq_nonneg (sin x * cos x - 1 / 2), sq_nonneg (sin x * cos x + 1 / 2), 
        h14, h15, mul_nonneg (show 0 ≤ sin x * cos x + 1 / 2 by nlinarith) (show 0 ≤ 1 / 2 - sin x * cos x by nlinarith)]
    constructor
    · -- Show 0 ≤ y
      nlinarith [hx, eq3, h16]
    · -- Show y ≤ 9 / 8
      nlinarith [hx, eq3, h18]
  · -- Now show the reverse: for any y ∈ [0, 9/8], there exists some x with f(x) = y.
    rintro ⟨hy1, hy2⟩
    use (1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4))
    have h12 : f ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4))) = sin ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ^ 4 - sin ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) * cos ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) + cos ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ^ 4 := h₀ ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)))
    have eq1 : sin ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) * cos ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) = ((-1 + Real.sqrt (9 - 8 * y)) / 4) := by
      have h11 : sin (2 * ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ) = 2 * sin ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) * cos ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) := by
        rw [show 2 * ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) = 2 * ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) by rfl]
        rw [sin_two_mul]
      have h12 : sin (2 * ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ) = (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4) ) := by
        have h13 : 2 * ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) = arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4) ) := by
          ring
        rw [h13]
        apply sin_arcsin
        · -- Show that $2 * ((-1 + \sqrt{9 - 8 * y}) / 4) \geq -1$
          nlinarith [Real.sqrt_nonneg (9 - 8 * y), Real.sq_sqrt (show (0 : ℝ) ≤ 9 - 8 * y by nlinarith)]
        · -- Show that $2 * ((-1 + \sqrt{9 - 8 * y}) / 4) \leq 1$
          nlinarith [Real.sqrt_nonneg (9 - 8 * y), Real.sq_sqrt (show (0 : ℝ) ≤ 9 - 8 * y by nlinarith)]
      nlinarith [h11, h12]
    have eq3 : sin ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ^ 2 + cos ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ^ 2 = 1 := by
      have h14 : sin ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ^ 2 + cos ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ^ 2 = 1 := by
        apply Real.sin_sq_add_cos_sq
      linarith
    have eq4 : sin ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ^ 4 + cos ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ^ 4 = (1 - 2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4) ^ 2) := by
      have h14 : sin ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ^ 2 + cos ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ^ 2 = 1 := by
        apply Real.sin_sq_add_cos_sq
      have h15 : sin ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ^ 4 + cos ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ^ 4 = (sin ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ^ 2 + cos ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ^ 2) ^ 2 - 2 * (sin ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) * cos ((1 / 2) * arcsin (2 * ((-1 + Real.sqrt (9 - 8 * y)) / 4)) ) ) ^ 2 := by
        nlinarith
      rw [h15, h14, eq1]
      <;> nlinarith
    rw [h12]
    nlinarith [Real.sqrt_nonneg (9 - 8 * y), Real.sq_sqrt (show (0 : ℝ) ≤ 9 - 8 * y by nlinarith)]