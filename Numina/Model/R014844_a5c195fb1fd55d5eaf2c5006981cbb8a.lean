import Mathlib

theorem algebra_99647 {x y : ℝ} (h₀ : 0 ≤ 1 - 3 * x) (h₁ : 0 ≤ 5 * y - 3 * x)
    (h₂ : 0 ≤ 5 - 5 * y) (h₃ : 0 ≤ 5 * y - 3 * x) :
    Real.sqrt (1 - 3 * x) - 1 = Real.sqrt (5 * y - 3 * x) ∧
    Real.sqrt (5 - 5 * y) + Real.sqrt (5 * y - 3 * x) = 5 ↔
    x = -8 / 3 ∧ y = -4 / 5 := by
  constructor
  · -- Assume both equations hold, prove (x, y) = (-8/3, -4/5)
    rintro ⟨h_eq1, h_eq2⟩
    have eq1 : Real.sqrt (1 - 3 * x) - 1 = Real.sqrt (5 * y - 3 * x) := h_eq1
    have eq1a : (Real.sqrt (1 - 3 * x) - 1) ^ 2 = (Real.sqrt (5 * y - 3 * x)) ^ 2 := by
      rw [eq1]
    have eq1b : (Real.sqrt (1 - 3 * x) - 1) ^ 2 = (Real.sqrt (1 - 3 * x)) ^ 2 - 2 * Real.sqrt (1 - 3 * x) + 1 := by
      ring
    have eq1c : (Real.sqrt (5 * y - 3 * x)) ^ 2 = 5 * y - 3 * x := by
      apply Real.sq_sqrt
      linarith
    have eq1d : (Real.sqrt (1 - 3 * x) - 1) ^ 2 = (1 - 3 * x) - 2 * Real.sqrt (1 - 3 * x) + 1 := by
      have h4 : (Real.sqrt (1 - 3 * x)) ^ 2 = 1 - 3 * x := by
        apply Real.sq_sqrt
        linarith
      rw [eq1b, h4]
    -- Expanding and equating to substituting squaring operation
    have eq2 : 2 - 5 * y = 2 * Real.sqrt (1 - 3 * x) := by
      nlinarith [eq1a, eq1c, eq1d]
    have eq3 : (2 - 5 * y) ^ 2 = 4 * (1 - 3 * x) := by
      calc
        (2 - 5 * y) ^ 2 = (2 * Real.sqrt (1 - 3 * x)) ^ 2 := by
          rw [eq2]
        _ = 4 * (Real.sqrt (1 - 3 * x) ) ^ 2 := by
          ring
        _ = 4 * (1 - 3 * x) := by
          have h44 : (Real.sqrt (1 - 3 * x)) ^ 2 = 1 - 3 * x := by
            apply Real.sq_sqrt
            linarith
          rw [h44]
    have eq4 : Real.sqrt (5 - 5 * y) = 6 - Real.sqrt (1 - 3 * x) := by
      nlinarith [h_eq2, eq2]
    have eq5 : (Real.sqrt (5 - 5 * y)) ^ 2 = (6 - Real.sqrt (1 - 3 * x))  ^ 2 := by
      rw [eq4]
    have eq6 : (Real.sqrt (5 - 5 * y)) ^ 2 = 5 - 5 * y := by
      apply Real.sq_sqrt
      linarith
    have eq7 : (6 - Real.sqrt (1 - 3 * x)) ^ 2 = 36 - 12 * Real.sqrt (1 - 3 * x) + (Real.sqrt (1 - 3 * x)) ^ 2 := by
      ring
    have eq8 : (Real.sqrt (1 - 3 * x)) ^ 2 = 1 - 3 * x := by
      apply Real.sq_sqrt
      linarith
    -- Solving both substitutions from squaring operation.
    have h5 : x = -8 / 3 := by
      nlinarith [sq_nonneg (x + 8 / 3), sq_nonneg (y + 4 / 5), Real.sqrt_nonneg (1 - 3 * x), Real.sqrt_nonneg (5 - 5 * y), Real.sqrt_nonneg (5 * y - 3 * x)]
    have h6 : y = -4 / 5 := by
      nlinarith [h5, sq_nonneg (y + 4 / 5), Real.sqrt_nonneg (1 - 3 * x), Real.sqrt_nonneg (5 - 5 * y), Real.sqrt_nonneg (5 * y - 3 * x)]
    exact ⟨h5, h6⟩
  · -- Backward direction. Assume (x, y) = (-8/3, -4/5), prove both equations.
    rintro ⟨h_eqx, h_eqy⟩
    constructor
    · -- Prove the first equation
      have h7 : Real.sqrt (1 - 3 * x) = 3 := by
        rw [h_eqx]
        rw [show (1 - 3 * (-8 / 3 : ℝ)) = (9 : ℝ) by norm_num]
        exact Real.sqrt_eq_cases.2 (by norm_num)
      have h8 : Real.sqrt (5 * y - 3 * x) = 2 := by
        rw [h_eqx, h_eqy]
        rw [show (5 * (-4 / 5 : ℝ) - 3 * (-8 / 3 : ℝ)) = (4 : ℝ) by norm_num]
        exact Real.sqrt_eq_cases.2 (by norm_num)
      linarith [h7, h8]
    · -- Prove the second equation
      have h7 : Real.sqrt (1 - 3 * x) = 3 := by
        rw [h_eqx]
        rw [show (1 - 3 * (-8 / 3 : ℝ)) = (9 : ℝ) by norm_num]
        exact Real.sqrt_eq_cases.2 (by norm_num)
      have h8 : Real.sqrt (5 * y - 3 * x) = 2 := by
        rw [h_eqx, h_eqy]
        rw [show (5 * (-4 / 5 : ℝ) - 3 * (-8 / 3 : ℝ)) = (4 : ℝ) by norm_num]
        exact Real.sqrt_eq_cases.2 (by norm_num)
      have h9 : Real.sqrt (5 - 5 * y) = 3 := by
        rw [h_eqy]
        rw [show (5 - 5 * (-4 / 5 : ℝ)) = (9 : ℝ) by norm_num]
        exact Real.sqrt_eq_cases.2 (by norm_num)
      nlinarith [h7, h8, h9]