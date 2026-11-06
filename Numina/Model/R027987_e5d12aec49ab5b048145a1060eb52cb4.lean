import Mathlib

theorem algebra_320470 (p : ℝ) :
    (∃! x : ℝ, x^4 + 6 * x^3 + 9 * x^2 - 3 * p * x^2 - 9 * p * x + 2 * p^2 = 0) ↔
    p = -9 / 4 := by
  constructor
  · -- If there exists a unique real solution, then p = -9/4
    intro h
    rcases h with ⟨x, ⟨hx1, hx2⟩⟩
    have h_eq : x^4 + 6 * x^3 + 9 * x^2 - 3 * p * x^2 - 9 * p * x + 2 * p^2 = 0 := hx1
    have h2 : ∀ y : ℝ, y^4 + 6 * y^3 + 9 * y^2 - 3 * p * y^2 - 9 * p * y + 2 * p^2 = 0 → y = x := by
      intro y hy
      have h3 := hx2 y hy
      simpa using h3
    have h3 := h2 (-3 - x) (by
      nlinarith [sq_nonneg (x + 3 / 2), sq_nonneg (x^2 + 3 * x + p), sq_nonneg (x^2 + 3 * x - p), sq_nonneg (x + 3 / 2)]
    )
    have h4 : x = (-3 - x) := by linarith
    have h5 : x = -3 / 2 := by
      linarith
      <;> nlinarith
    rw [h5] at h_eq
    have h_eq2 : 32 * p^2 + 108 * p + 81 = 0 := by
      nlinarith
    have hp : (p + 9 / 4) * (2 * p + 9 / 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp hp) with hp1 hp2
    · -- p + 9/4 = 0, so p = -9/4
      linarith
    · -- 2p + 9/4 = 0, so p = -9/8
      -- This case is impossible because it would imply another solution.
      exfalso
      have hp2' : p = -9 / 8 := by linarith
      have h_eq3 : (∃ y : ℝ, y^4 + 6 * y^3 + 9 * y^2 - 3 * p * y^2 - 9 * p * y + 2 * p^2 = 0 ∧ y ≠ x) := by
        use (-3 - 3 * Real.sqrt (1/2)) / 2
        constructor
        · -- Show that (-3 - 3 * Real.sqrt (1 / 2)) / 2 is a solution when p = -9 / 8
          rw [hp2']
          nlinarith [Real.sqrt_nonneg (1 / 2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)]
        · -- Show that (-3 - 3 * Real.sqrt (1 / 2)) / 2 ≠ x
          have hx6 : x = -3 / 2 := by linarith
          rw [hx6]
          by_contra h7
          have h8 : Real.sqrt (1 / 2) = 0 := by
            nlinarith
          have h9 : Real.sqrt (1 / 2) > 0 := by
            apply Real.sqrt_pos.mpr
            all_goals norm_num
          linarith
      rcases h_eq3 with ⟨y, hy1, hy2⟩
      have hy3 : y = x := by
        apply h2 y hy1
      contradiction
  · -- p = -9/4 implies existence of unique real solution
    intro hp
    rw [hp] at *
    use -3 / 2
    constructor
    · -- Show that -3/2 is a solution.
      norm_num
    · -- Show that -3/2 is a unique solution
      intro y hy
      have h_eq : y ^ 4 + 6 * y ^ 3 + 9 * y ^ 2 - 3 * (-9 / 4) * y ^ 2 - 9 * (-9 / 4) * y + 2 * (-9 / 4) ^ 2 = 0 := by linarith [hy]
      have h_eq2 : (y + 3 / 2) ^ 2 * ((y + 3 / 2) ^ 2) = 0 := by
        nlinarith [sq_nonneg (y + 3 / 2), sq_nonneg ((y ^ 2 + 3 * y) + 9 / 4), sq_nonneg ((y + 3 / 2) ^ 2), sq_nonneg ((y + 3 / 2) * (y ^ 2 + 3 * y + 9 / 4)), sq_nonneg (y ^ 2 + 3 * y + 9 / 4)]
      cases' (mul_eq_zero.mp h_eq2) with h_eq3 h_eq4
      · -- (y + 3/2)^2 = 0
        have : y + 3 / 2 = 0 := by 
          apply pow_eq_zero 
          exact h_eq3
        linarith
      · -- (y + 3/2)^2 = 0
        have : y + 3 / 2 = 0 := by 
          apply pow_eq_zero 
          exact h_eq4
        linarith