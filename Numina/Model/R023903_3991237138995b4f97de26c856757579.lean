import Mathlib


open Real Set


theorem algebra_302147 (a b : ℝ) (ha : a ∈ Set.Icc 1 3) (hb : b ∈ Set.Icc 1 3)
    (h : a + b = 4) :
    |Real.sqrt (a + 1 / a) - Real.sqrt (b + 1 / b)| ≤
    Real.sqrt (10 / 3) - Real.sqrt 2 := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with  ⟨hb1, hb2⟩
  have h1 : 1 ≤ a := by linarith
  have h2 : a ≤ 3 := by linarith
  have h3 : 1 ≤ b := by linarith
  have h4 : b ≤ 3 := by linarith
  have h5 : b = 4 - a := by linarith
  have h6 : Real.sqrt (a + 1 / a) - Real.sqrt (b + 1 / b) ≤ Real.sqrt (10 / 3) - Real.sqrt 2 := by
    have h7 : Real.sqrt (a + 1 / a) ≤ Real.sqrt (10 / 3 : ℝ) := by
      have h8 : a + 1 / a ≤ (10 / 3 : ℝ) := by
        have h9 : 0 < a := by nlinarith
        have h10 : a + 1 / a - (10 / 3 : ℝ) ≤ 0 := by
          have h11 : a + 1 / a - (10 / 3 : ℝ) = (3 * a ^ 2 - 10 * a + 3) / (3 * a) := by
            field_simp
            nlinarith
          rw [h11]
          have h13 : 3 * a ^ 2 - 10 * a + 3 ≤ 0 := by
            nlinarith [sq_nonneg (a - 3 : ℝ), sq_nonneg (a - 1 / 3 : ℝ), sq_nonneg (a - 1 : ℝ), sq_nonneg (a - 3 : ℝ)]
          have h14 : (3 * a ^ 2 - 10 * a + 3) / (3 * a) ≤ 0 := by
            apply div_nonpos_of_nonpos_of_nonneg
            linarith
            nlinarith
          linarith
        linarith
      have h15 : Real.sqrt (a + 1 / a) ≤ Real.sqrt (10 / 3 : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith
      linarith
    have h11 : Real.sqrt (b + 1 / b) ≥ Real.sqrt 2 := by
      have h12 : b + 1 / b ≥ (2 : ℝ) := by
        have h13 : 0 < b := by nlinarith
        have h14 : b + 1 / b - 2 ≥ 0 := by
          have h15 : b + 1 / b - 2 = (b ^ 2 - 2 * b + 1) / b := by
            field_simp
            nlinarith
          rw [h15]
          have h16 : b ^ 2 - 2 * b + 1 ≥ 0 := by
            have h17 : b ^ 2 - 2 * b + 1 = (b - 1) ^ 2 := by
              ring
            rw [h17]
            nlinarith
          have h17 : (b ^ 2 - 2 * b + 1) / b ≥ 0 := by
            apply div_nonneg
            linarith
            nlinarith
          linarith
        linarith
      have h18 : Real.sqrt (b + 1 / b) ≥ Real.sqrt (2 : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith
      linarith
    nlinarith
  have h7 : Real.sqrt (a + 1 / a) - Real.sqrt (b + 1 / b) ≥ Real.sqrt 2 - Real.sqrt (10 / 3 : ℝ) := by
    have h13 : Real.sqrt (a + 1 / a) ≥ Real.sqrt 2 := by
      have h14 : a + 1 / a ≥ (2 : ℝ) := by
        have h15 : 0 < a := by nlinarith
        have h16 : a + 1 / a - 2 ≥ 0 := by
          have h17 : a + 1 / a - 2 = (a ^ 2 - 2 * a + 1) / a := by
            field_simp
            nlinarith
          rw [h17]
          have h18 : a ^ 2 - 2 * a + 1 ≥ 0 := by
            have h19 : a ^ 2 - 2 * a + 1 = (a - 1) ^ 2 := by
              ring
            rw [h19]
            nlinarith
          have h19 : (a ^ 2 - 2 * a + 1) / a ≥ 0 := by
            apply div_nonneg
            linarith
            nlinarith
          linarith
        linarith
      have h20 : Real.sqrt (a + 1 / a) ≥ Real.sqrt (2 : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith
      linarith
    have h14 : Real.sqrt (b + 1 / b) ≤ Real.sqrt (10 / 3 : ℝ) := by
      have h15 : b + 1 / b ≤ (10 / 3 : ℝ) := by
        have h16 : 0 < b := by nlinarith
        have h17 : b + 1 / b - (10 / 3 : ℝ) ≤ 0 := by
          have h18 : b + 1 / b - (10 / 3 : ℝ) = (3 * b ^ 2 - 10 * b + 3) / (3 * b) := by
            field_simp
            nlinarith
          rw [h18]
          have h19 : 3 * b ^ 2 - 10 * b + 3 ≤ 0 := by
            nlinarith [sq_nonneg (b - 3 : ℝ), sq_nonneg (b - 1 / 3 : ℝ), sq_nonneg (b - 1 : ℝ), sq_nonneg (b - 3 : ℝ)]
          have h20 : (3 * b ^ 2 - 10 * b + 3) / (3 * b) ≤ 0 := by
            apply div_nonpos_of_nonpos_of_nonneg
            linarith
            nlinarith
          linarith
        linarith
      have h21 : Real.sqrt (b + 1 / b) ≤ Real.sqrt (10 / 3 : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith
      linarith
    nlinarith
  have h8 : - (Real.sqrt (10 / 3) - Real.sqrt 2) ≤ Real.sqrt (a + 1 / a) - Real.sqrt (b + 1 / b) := by
    linarith [h7]
  have h9 : Real.sqrt (a + 1 / a) - Real.sqrt (b + 1 / b) ≤ Real.sqrt (10 / 3) - Real.sqrt 2 := by
    linarith [h6]
  apply abs_le.mpr
  constructor
  · linarith [h8]
  · linarith [h9]