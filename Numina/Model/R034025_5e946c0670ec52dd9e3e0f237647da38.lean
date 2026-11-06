import Mathlib

theorem algebra_328244 (x : Fin 3 → ℝ) (hx : ∀ i, x i ≥ (i + 1)^2) :
    Real.sqrt (x 0 - 1) + 2 * Real.sqrt (x 1 - 4) + 3 * Real.sqrt (x 2 - 9) =
    (x 0 + x 1 + x 2) / 2 ↔ x 0 = 2 ∧ x 1 = 8 ∧ x 2 = 18 := by
  constructor
  · -- Forward direction: if the equality holds, then (x0, x1, x2) = (2, 8, 18)
    intro h
    have h1 : Real.sqrt (x 0 - 1) + 2 * Real.sqrt (x 1 - 4) + 3 * Real.sqrt (x 2 - 9) =
        (x 0 + x 1 + x 2) / 2 := h
    have h2 : Real.sqrt (x 0 - 1) ≥ 0 := by positivity
    have h3 : Real.sqrt (x 1 - 4) ≥ 0 := by positivity
    have h4 : Real.sqrt (x 2 - 9) ≥ 0 := by positivity
    have h5 : x 0 ≥ 1 := by
      specialize hx 0
      norm_num at hx ⊢
      linarith
    have h6 : x 1 ≥ 4 := by
      specialize hx 1
      norm_num at hx ⊢
      linarith
    have h7 : x 2 ≥ 9 := by
      specialize hx 2
      norm_num at hx ⊢
      linarith
    have h8 : (Real.sqrt (x 0 - 1) - 1) ^ 2 + (Real.sqrt (x 1 - 4) - 2) ^ 2 + (Real.sqrt (x 2 - 9) - 3) ^ 2 = 0 := by
      nlinarith [Real.sqrt_nonneg (x 0 - 1), Real.sqrt_nonneg (x 1 - 4), Real.sqrt_nonneg (x 2 - 9),
        Real.sq_sqrt (show (0 : ℝ) ≤ x 0 - 1 by linarith),
        Real.sq_sqrt (show (0 : ℝ) ≤ x 1 - 4 by linarith),
        Real.sq_sqrt (show (0 : ℝ) ≤ x 2 - 9 by linarith),
        sq_nonneg (Real.sqrt (x 0 - 1) - 1), sq_nonneg (Real.sqrt (x 1 - 4) - 2), sq_nonneg (Real.sqrt (x 2 - 9) - 3)
      ]
    have h9 : Real.sqrt (x 0 - 1) - 1 = 0 := by
      nlinarith [sq_nonneg (Real.sqrt (x 0 - 1) - 1), sq_nonneg (Real.sqrt (x 1 - 4) - 2), sq_nonneg (Real.sqrt (x 2 - 9) - 3), h8]
    have h10 : Real.sqrt (x 0 - 1) = 1 := by linarith
    have h11 : Real.sqrt (x 1 - 4) - 2 = 0 := by
      nlinarith [sq_nonneg (Real.sqrt (x 0 - 1) - 1), sq_nonneg (Real.sqrt (x 1 - 4) - 2), sq_nonneg (Real.sqrt (x 2 - 9) - 3), h8]
    have h12 : Real.sqrt (x 1 - 4) = 2 := by linarith
    have h13 : Real.sqrt (x 2 - 9) - 3 = 0 := by
      nlinarith [sq_nonneg (Real.sqrt (x 0 - 1) - 1), sq_nonneg (Real.sqrt (x 1 - 4) - 2), sq_nonneg (Real.sqrt (x 2 - 9) - 3), h8]
    have h14 : Real.sqrt (x 2 - 9) = 3 := by linarith
    have h15 : x 0 - 1 = 1 := by
      calc
        x 0 - 1 = (Real.sqrt (x 0 - 1)) ^ 2 := by rw [Real.sq_sqrt]; linarith
        _ = 1 ^ 2 := by rw [h10]
        _ = (1 : ℝ) := by norm_num
    have h16 : x 0 = 2 := by linarith
    have h17 : x 1 - 4 = 4 := by
      calc
        x 1 - 4 = (Real.sqrt (x 1 - 4)) ^ 2 := by rw [Real.sq_sqrt]; linarith
        _ = 2 ^ 2 := by rw [h12]
        _ = (4 : ℝ) := by norm_num
    have h18 : x 1 = 8 := by linarith
    have h19 : x 2 - 9 = 9 := by
      calc
        x 2 - 9 = (Real.sqrt (x 2 - 9)) ^ 2 := by rw [Real.sq_sqrt]; linarith
        _ = 3 ^ 2 := by rw [h14]
        _ = (9 : ℝ) := by norm_num
    have h20 : x 2 = 18 := by linarith
    constructor
    · exact h16
    constructor
    · exact h18
    · exact h20
  · -- Backward direction: if (x0, x1, x2) = (2, 8, 18), then the equality holds
    rintro ⟨hx0, hx1, hx2⟩
    have h1 : Real.sqrt (x 0 - 1) = 1 := by
      rw [hx0]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (x 1 - 4) = 2 := by
      rw [hx1]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt (x 2 - 9) = 3 := by
      rw [hx2]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3]
    rw [hx0, hx1, hx2]
    all_goals norm_num