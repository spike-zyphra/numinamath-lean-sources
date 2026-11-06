import Mathlib

theorem algebra_316417 {a b : ℝ} (h : abs (a - 1) + Real.sqrt ((a - 2) * (b - 2) ^ 2) + abs (b ^ 2 + 1) = a) :
    a ^ b = 1 := by

  have h1 : abs (b ^ 2 + 1) = b ^ 2 + 1 := by
    rw [abs_of_nonneg]
    nlinarith [sq_nonneg b]

  rw [h1] at h

  by_cases h6 : a ≥ 2
  · -- Case a ≥ 2
    have h7 : Real.sqrt ((a - 2) * (b - 2) ^ 2) = Real.sqrt (a - 2) * abs (b - 2) := by
      have h8 : (a - 2) * (b - 2) ^ 2 ≥ 0 := by nlinarith [sq_nonneg (b - 2), h6]
      have h9 : Real.sqrt ((a - 2) * (b - 2) ^ 2) = Real.sqrt ((a - 2) * (b - 2) ^ 2) := by rfl
      have h12 : Real.sqrt ((a - 2) * (b - 2) ^ 2) = Real.sqrt (a - 2) * abs (b - 2) := by
        calc
          Real.sqrt ((a - 2) * (b - 2) ^ 2)
              = Real.sqrt ((a - 2) * (b - 2) ^ 2) := by rfl
          _ = Real.sqrt ((a - 2) * (b - 2) ^ 2) := by ring_nf
          _ = Real.sqrt (a - 2) * Real.sqrt ((b - 2) ^ 2) := by 
            rw [Real.sqrt_mul (by nlinarith [sq_nonneg (b - 2), h6])]
          _ = Real.sqrt (a - 2) * abs (b - 2) := by
            rw [Real.sqrt_sq_eq_abs]
      linarith
    rw [h7] at h

    have h8 : abs (a - 1) = a - 1 := by
      rw [abs_of_nonneg]
      nlinarith
    rw [h8] at h

    have h9 : Real.sqrt (a - 2) * abs (b - 2) + b ^ 2 = 0 := by
      nlinarith [Real.sqrt_nonneg (a - 2), abs_nonneg (b - 2), sq_nonneg b]

    have h10 : b ^ 2 = 0 := by 
      nlinarith [Real.sqrt_nonneg (a - 2), abs_nonneg (b - 2), sq_nonneg b]

    have h11 : b = 0 := by
      simp at h10 ⊢
      linarith

    have h12 : Real.sqrt (a - 2) * abs (b - 2) = 0 := by
      nlinarith [Real.sqrt_nonneg (a - 2), abs_nonneg (b - 2), sq_nonneg b]

    have h13 : Real.sqrt (a - 2) = 0 ∨ abs (b - 2) = 0 := by
      cases (mul_eq_zero.mp h12) with
      | inl h13 =>
        left
        linarith [Real.sqrt_nonneg (a - 2), abs_nonneg (b - 2)]
      | inr h14 =>
        right
        linarith [Real.sqrt_nonneg (a - 2), abs_nonneg (b - 2)]

    cases h13 with
    | inl h14 =>
      have h15 : a - 2 = 0 := by
        rw [Real.sqrt_eq_zero (by linarith)] at h14
        linarith
      have ha : a = 2 := by linarith
      rw [ha, h11]
      norm_num

    | inr h16 =>
      have h17 : b - 2 = 0 := by
        rw [abs_eq_zero] at h16
        linarith
      have hb : b = 2 := by linarith
      exfalso
      linarith [show b = 0 from h11]

  · -- Case a < 2
    have h7 : Real.sqrt ((a - 2) * (b - 2) ^ 2) = 0 := by
      have h8 : (a - 2) * (b - 2) ^ 2 ≤ 0 := by nlinarith [sq_nonneg (b - 2), show a - 2 < 0 by linarith]
      rw [Real.sqrt_eq_zero'] <;> linarith

    rw [h7] at h
    by_cases h8 : a ≥ 1
    · -- Case 1 ≤ a < 2
      have h9 : abs (a - 1) = a - 1 := by
        rw [abs_of_nonneg]
        nlinarith
      rw [h9] at h
      have h10 : b ^ 2 = 0 := by
        nlinarith [abs_nonneg (b ^ 2 + 1), sq_nonneg (b), h8]

      have hb : b = 0 := by
        simp at h10 ⊢
        exact h10

      rw [hb]
      simp [show a ≠ 0 by nlinarith]

    · -- Case a < 1
      have h9 : abs (a - 1) = 1 - a := by
        rw [abs_of_neg (by linarith : a - 1 < 0)]
        linarith
      rw [h9] at h
      nlinarith [sq_nonneg b, show 2 * a - 2 < 0 by nlinarith]