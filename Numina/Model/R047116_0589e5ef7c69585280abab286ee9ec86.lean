import Mathlib

theorem algebra_15829 : {x : ℝ | ∃a b, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ x = 1 / a + 1 / b} = Set.Ici 4 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · -- Assume x ∈ {y | ∃ a b > 0, a + b = 1, y = 1/a + 1/b}
    rintro ⟨a, b, ha, hb, h1, hx⟩
    have h2 : 1 / a + 1 / b = (a + b) / (a * b) := by
      field_simp
      <;> ring
    have h3 : a * b ≤ (1 / 4 : ℝ) := by
      have h4 : (a + b : ℝ) ^ 2 = 1 := by
        rw [h1]
        all_goals norm_num
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1)]
    have hx2 : x = 1 / (a * b) := by
      rw [hx]
      rw [h2]
      rw [h1]
      all_goals norm_num
    have hx3 : x ≥ 4 := by
      rw [hx2]
      have h4 : a * b ≤ (1 / 4 : ℝ) := h3
      have h5 : (a * b : ℝ) > 0 := by
        nlinarith
      have h6 : 1 / (a * b : ℝ) ≥ (4 : ℝ) := by
        have h7 : a * b ≤ (1 / 4 : ℝ) := h4
        have h8 : a * b > 0 := h5
        apply (le_div_iff₀ (by linarith)).mpr
        nlinarith
      linarith
    linarith
  · -- Assume x ≥ 4
    intro hx
    have h1 : x ≥ 4 := by
      linarith
    use (x - Real.sqrt (x ^ 2 - 4 * x)) / (2 * x)
    use (x + Real.sqrt (x ^ 2 - 4 * x)) / (2 * x)
    constructor
    · -- Show 0 < a
      have h4 : x ^ 2 - 4 * x ≥ 0 := by
        nlinarith
      have h6 : x - Real.sqrt (x ^ 2 - 4 * x) > 0 := by
        have h7 : Real.sqrt (x ^ 2 - 4 * x) < x := by
          nlinarith [Real.sqrt_nonneg (x ^ 2 - 4 * x), Real.sq_sqrt (show (x ^ 2 - 4 * x) ≥ 0 by nlinarith)]
        nlinarith
      have h7 : (x - Real.sqrt (x ^ 2 - 4 * x) : ℝ) / (2 * x) > 0 := by
        apply div_pos
        linarith
        nlinarith
      linarith
    constructor
    · -- Show 0 < b
      have h8 : x + Real.sqrt (x ^ 2 - 4 * x) > 0 := by
        have h11 : Real.sqrt (x ^ 2 - 4 * x) ≥ 0 := by
          apply Real.sqrt_nonneg
        nlinarith [Real.sq_sqrt (show (x ^ 2 - 4 * x) ≥ 0 by nlinarith)]
      have h9 : (x + Real.sqrt (x ^ 2 - 4 * x) : ℝ) / (2 * x) > 0 := by
        apply div_pos
        linarith
        nlinarith
      linarith
    constructor
    · -- Show a + b = 1
      field_simp
      <;> ring_nf
      <;> norm_num
    · -- Show x = 1 / a + 1 / b
      field_simp [(show (x - Real.sqrt (x ^ 2 - 4 * x) : ℝ) ≠ 0 by
        by_contra h
        have h7 : x - Real.sqrt (x ^ 2 - 4 * x) = 0 := by
          linarith
        have h8 : Real.sqrt (x ^ 2 - 4 * x) = x := by
          nlinarith
        have h9 : (x ^ 2 - 4 * x : ℝ) = x ^ 2 := by
          calc
            (x ^ 2 - 4 * x : ℝ) = (Real.sqrt (x ^ 2 - 4 * x)) ^ 2 := by
              rw [Real.sq_sqrt]
              nlinarith
            _ = x ^ 2 := by
              rw [h8]
        have h10 : x = 0 := by
          nlinarith
        linarith
      ), (show (x + Real.sqrt (x ^ 2 - 4 * x) : ℝ) ≠ 0 by
        by_contra h
        have h7 : x + Real.sqrt (x ^ 2 - 4 * x) = 0 := by
          linarith
        nlinarith [Real.sqrt_nonneg (x ^ 2 - 4 * x), Real.sq_sqrt (show (x ^ 2 - 4 * x) ≥ 0 by nlinarith)]
      )
      ]
      <;> nlinarith [Real.sqrt_nonneg (x ^ 2 - 4 * x), Real.sq_sqrt (show (x ^ 2 - 4 * x) ≥ 0 by nlinarith)]