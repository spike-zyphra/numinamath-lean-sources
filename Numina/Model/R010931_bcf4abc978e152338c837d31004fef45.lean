import Mathlib

theorem algebra_203118 {x y : ℝ} (h : 0 ≤ x ∧ 0 ≤ y) : 
  x + 2 * Real.sqrt y = 2 ∧ 2 * Real.sqrt x + y = 2 ↔ x = 4 - 2 * Real.sqrt 3 ∧ y = 4 - 2 * Real.sqrt 3 := by
  constructor
  · -- Assume left side, prove right side.
    rintro ⟨h1, h2⟩
    have h3 : 0 ≤ x := h.1
    have h4 : 0 ≤ y := h.2
    have h5 : Real.sqrt y ≥ 0 := by positivity
    have h6 : Real.sqrt x ≥ 0 := by positivity
    have eq1 : Real.sqrt y ^ 2 = y := by
      rw [Real.sq_sqrt]
      linarith
    have eq2 : Real.sqrt x ^ 2 = x := by
      rw [Real.sq_sqrt]
      linarith
    have eq3 : Real.sqrt y = (2 - x) / 2 := by
      nlinarith 
    have eq4 : Real.sqrt x = (2 - y) / 2 := by
      nlinarith 
    have eq5 : y = ((2 - x) / 2) ^ 2 := by
      have eq6 : Real.sqrt y ^ 2 = y := eq1
      have eq7 : Real.sqrt y = (2 - x) / 2 := eq3
      rw [eq7] at eq6
      nlinarith
    have eq8 : x = ((2 - y) / 2) ^ 2 := by
      have eq9 : Real.sqrt x ^ 2 = x := eq2
      have eq10 : Real.sqrt x = (2 - y) / 2 := eq4
      rw [eq10] at eq9
      nlinarith
    have h7 : x = y := by 
      nlinarith [sq_nonneg (x - (4 - 2 * Real.sqrt 3)), sq_nonneg (y - (4 - 2 * Real.sqrt 3)), 
        Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
        ]
    have h9 : x = 4 - 2 * Real.sqrt 3 := by
      have h8 : x = y := h7
      have eq5' : y = ((2 - x) / 2) ^ 2 := eq5
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        Real.sqrt_nonneg x, Real.sqrt_nonneg y
      ]
    have h10 : y = 4 - 2 * Real.sqrt 3 := by
      nlinarith [h9, h7]
    constructor
    · exact h9
    · exact h10
  · -- Assume right side, prove left side.
    rintro ⟨h1, h2⟩
    constructor
    · -- First equation
      have h3 : 0 ≤ x := by linarith
      have h4 : 0 ≤ y := by linarith
      have eq1 : Real.sqrt y = Real.sqrt 3 - 1 := by
        have h5 : y = 4 - 2 * Real.sqrt 3 := h2
        rw [h5]
        have h6 : Real.sqrt (4 - 2 * Real.sqrt 3) = Real.sqrt 3 - 1 := by
          have h7 : Real.sqrt 3 ≥ 1 := by
            nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
          have h8 : Real.sqrt 3 - 1 ≥ 0 := by
            linarith [h7]
          have h9 : (Real.sqrt 3 - 1) ^ 2 = 4 - 2 * Real.sqrt 3 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
          rw [← h9]
          field_simp [Real.sqrt_sq h8]
        linarith
      rw [eq1]
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    · -- Second equation
      have h3 : 0 ≤ x := by linarith
      have h4 : 0 ≤ y := by linarith
      have eq1 : Real.sqrt x = Real.sqrt 3 - 1 := by
        have h11 : x = 4 - 2 * Real.sqrt 3 := h1
        rw [h11]
        have h6 : Real.sqrt (4 - 2 * Real.sqrt 3) = Real.sqrt 3 - 1 := by
          have h7 : Real.sqrt 3 ≥ 1 := by
            nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
          have h8 : Real.sqrt 3 - 1 ≥ 0 := by
            linarith [h7]
          have h9 : (Real.sqrt 3 - 1) ^ 2 = 4 - 2 * Real.sqrt 3 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
          rw [← h9]
          field_simp [Real.sqrt_sq h8]
        linarith
      rw [eq1]
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]