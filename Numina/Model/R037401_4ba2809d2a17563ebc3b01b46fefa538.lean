import Mathlib

theorem algebra_285263 (a : ℝ) :
  {a : ℝ | ∃ x y : ℝ, Real.cos x ^ 2 - 2 * Real.cos x * Real.cos y * Real.cos (x + y) +
    Real.cos (x + y) ^ 2 = a} = {a : ℝ | 0 ≤ a ∧ a ≤ 1} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Forward implication: a must be in the range [0,1]
    intro ha
    rcases ha with ⟨x, y, hxy⟩
    have h3 : Real.cos x ^ 2 - 2 * Real.cos x * Real.cos y * Real.cos (x + y) + Real.cos (x + y) ^ 2 =
        (Real.sin y) ^ 2 := by
      have h2 : Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y := by
        rw [Real.cos_add]
      rw [h2]
      have h4 : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
      have h5 : Real.cos y ^ 2 + Real.sin y ^ 2 = 1 := Real.cos_sq_add_sin_sq y
      have h6 : Real.cos x ^ 2 - 2 * Real.cos x * Real.cos y * (Real.cos x * Real.cos y - Real.sin x * Real.sin y) + (Real.cos x * Real.cos y - Real.sin x * Real.sin y) ^ 2 = (Real.sin y) ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, sq_nonneg (Real.cos x - Real.cos y), sq_nonneg (Real.sin x - Real.sin y), sq_nonneg (Real.cos x * Real.sin y - Real.sin x * Real.cos y)]
      linarith
    have ha1 : a = (Real.sin y) ^ 2 := by
      linarith [hxy, h3]
    rw [ha1]
    constructor
    · -- Show 0 ≤ a
      nlinarith [sq_nonneg (Real.sin y)]
    · -- Show a ≤ 1
      nlinarith [Real.sin_sq_add_cos_sq y, sq_nonneg (Real.sin y), sq_nonneg (Real.cos y)]
  · -- Backward implication: For any a in [0, 1], there's some x,y.
    intro ha
    rcases ha with ⟨ha1, ha2⟩
    use (0 : ℝ)
    use (Real.arcsin (Real.sqrt a))
    have h1 : Real.cos (0 : ℝ) = 1 := Real.cos_zero
    have h2 : Real.cos (Real.arcsin (Real.sqrt a)) = Real.sqrt (1 - a) := by
      rw [Real.cos_arcsin]
      have h8 : (Real.sqrt a) ^ 2 = a := by
        rw [Real.sq_sqrt]
        linarith
      have h5 : 1 - (Real.sqrt a) ^ 2 = 1 - a := by
        linarith [h8]
      rw [h5]
    have h3 : Real.cos (0 + Real.arcsin (Real.sqrt a)) = Real.sqrt (1 - a) := by
      have h4 : Real.cos (0 + Real.arcsin (Real.sqrt a)) = Real.cos (Real.arcsin (Real.sqrt a)) := by
        ring_nf
      rw [h4]
      all_goals linarith [h2]
    have h7 : Real.cos (0 : ℝ) ^ 2 - 2 * Real.cos (0 : ℝ) * Real.cos (Real.arcsin (Real.sqrt a)) * Real.cos (0 + Real.arcsin (Real.sqrt a)) + Real.cos (0 + Real.arcsin (Real.sqrt a)) ^ 2 = a := by
      rw [h1]
      rw [h3]
      rw [h2]
      have h4 : (Real.sqrt (1 - a)) ^ 2 = (1 - a) := Real.sq_sqrt (by linarith)
      nlinarith [Real.sqrt_nonneg (1 - a), h4, Real.sq_sqrt (show (0 : ℝ) ≤ (1 - a : ℝ) by linarith)]
    linarith [h7]