import Mathlib

theorem algebra_10726 (a : ℝ) (ha : a ≠ 0) :
    (∃! x : ℝ, x^2 + a * abs x + a^2 - 3 = 0) ↔ a = Real.sqrt 3 := by
  constructor
  · -- Forward direction: If the equation has a unique solution, then a = sqrt(3).
    intro h
    rcases h with ⟨x, ⟨hx1, hx2⟩⟩
    have h1 : x^2 + a * abs x + a^2 - 3 = 0 := hx1
    have h2 : (-x)^2 + a * abs (-x) + a^2 - 3 = 0 := by
      have h3 : abs (-x) = abs x := by
        simp [abs_neg]
      rw [h3]
      nlinarith [h1]
    have h3 : -x = x := by
      have h4 : (-x)^2 + a * abs (-x) + a^2 - 3 = 0 := h2
      have h5 : (-x) = x := by
        apply hx2
        all_goals
          try linarith
      linarith
    have h4 : x = 0 := by
      linarith
    rw [h4] at h1
    have h5 : a^2 = 3 := by
      simp at h1
      nlinarith
    have h7 : a = Real.sqrt 3 ∨ a = -Real.sqrt 3 := by
      have h7 : a^2 = 3 := h5
      have h8 : a^2 - 3 = 0 := by linarith
      have h9 : (a - Real.sqrt 3) * (a + Real.sqrt 3) = 0 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      cases' (mul_eq_zero.mp h9) with h10 h11
      · left
        linarith
      · right
        nlinarith
    cases h7 with
    | inl ha2 =>
      tauto
    | inr ha2 =>
      have ha2 : a = -Real.sqrt 3 := by linarith
      have h8 : (Real.sqrt 3 : ℝ)^2 + a * abs (Real.sqrt 3 : ℝ) + a^2 - 3 = 0 := by
        rw [ha2]
        have h9 : abs ((Real.sqrt 3 : ℝ)) = Real.sqrt 3 := by
          apply abs_of_nonneg
          positivity
        rw [h9]
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h9 : (Real.sqrt 3 : ℝ) = x := by
        have h10 : (Real.sqrt 3 : ℝ)^2 + a * abs (Real.sqrt 3 : ℝ) + a^2 - 3 = 0 := h8
        have h11 : (Real.sqrt 3 : ℝ) = x := by
          apply hx2
          all_goals
            try linarith
        linarith
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  · -- Backward direction: If a = sqrt(3), then the equation has a unique solution.
    intro ha
    use 0
    constructor
    · -- Show that 0 is a solution
      rw [show a = Real.sqrt 3 by linarith [ha]]
      norm_num [abs_zero, Real.sq_sqrt]
    · -- Show that if y is a solution, then y = 0
      intro y hy
      have h10 : y^2 + a * abs y + a^2 - 3 = 0 := by
        linarith [hy]
      rw [show a = Real.sqrt 3 by linarith [ha]] at h10
      have h11 : y ^ 2 + Real.sqrt 3 * abs y = 0 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h14 : abs y = 0 := by
        have h12 : abs y ≥ 0 := abs_nonneg y
        have h13 : y ^ 2 ≥ 0 := sq_nonneg y
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), sq_nonneg (abs y), sq_nonneg (y)]
      have h15 : y = 0 := abs_eq_zero.mp h14
      linarith