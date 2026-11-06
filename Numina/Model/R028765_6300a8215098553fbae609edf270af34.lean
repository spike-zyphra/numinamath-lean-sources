import Mathlib

theorem algebra_255625 (x : ℝ) :
    ((x^3 + x)/3)^3 + (x^3 + x)/3 = 3 * x ↔ x = 0 ∨ x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
  constructor
  · -- Forward: If the equation holds, prove the root.
    intro h
    have h1 : (x ^ 3 + x) / 3 = x := by
      nlinarith [sq_nonneg ((x ^ 3 + x) / 3), sq_nonneg (x), sq_nonneg ((x ^ 3 + x) / 3 - x), sq_nonneg (x ^ 2 - 2)]
    have he : (x ^ 3 + x) / 3 = x := h1
    have eq3 : x ^ 3 + x = 3 * x := by
      linarith [he]
    have eq4 : x ^ 3 = 2 * x := by
      nlinarith
    have eq5 : x ^ 3 - 2 * x = 0 := by
      linarith
    have eq6 : x * (x ^ 2 - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq6) with eq7 eq8
    · -- Case 1 : x = 0
      left
      linarith
    · -- Case 2 : x^2 - 2 = 0, so x = ±√2
      have eq9 : x ^ 2 = (2 : ℝ) := by
        linarith
      have hx3 : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
        have h13 : x ^ 2 = (2 : ℝ) := eq9
        have h14 : x ^ 2 - (Real.sqrt 2) ^ 2 = 0 := by
          have h15 : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
          nlinarith
        have hx5 : (x - Real.sqrt 2) * (x + Real.sqrt 2) = 0 := by
          nlinarith [Real.sqrt_nonneg 2]
        cases' (mul_eq_zero.mp hx5) with hx6 hx7
        · -- x - Real.sqrt 2 = 0
          left
          linarith
        · -- x + Real.sqrt 2 = 0
          right
          nlinarith
          <;> nlinarith [Real.sqrt_nonneg 2]
      tauto
  · -- Backward: The roots satisfy the equation.
    intro h
    rcases h with (h_eq | h_eq | h_eq)
    · -- Case 1: x = 0
      rw [h_eq]
      norm_num
      all_goals linarith
    · -- Case 2: x = Real.sqrt 2
      rw [h_eq]
      have h5 : (Real.sqrt 2 : ℝ) ^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
      have eq3 : ((Real.sqrt 2 : ℝ) ^3 + (Real.sqrt 2 : ℝ)) / 3 = (Real.sqrt 2 : ℝ) := by
        have h1 : (Real.sqrt 2 : ℝ) ^3 = (2 * (Real.sqrt 2 : ℝ)) := by
          calc
            (Real.sqrt 2 : ℝ) ^3 = (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) ^2 := by ring
            _ = (Real.sqrt 2 : ℝ) * (2 : ℝ) := by rw [show (Real.sqrt 2 : ℝ) ^2 = (2 : ℝ) by linarith [h5]]
            _ = (2 * (Real.sqrt 2 : ℝ)) := by ring
        have h2 : (Real.sqrt 2 : ℝ) ^3 + (Real.sqrt 2 : ℝ) = 3 * (Real.sqrt 2 : ℝ) := by
          linarith [h1]
        field_simp [h2]
        <;> nlinarith
      rw [eq3]
      have h8 : (Real.sqrt 2 : ℝ) ^3 = 2 * (Real.sqrt 2 : ℝ) := by
        calc
          (Real.sqrt 2 : ℝ) ^3 = (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) ^2 := by ring
          _ = (Real.sqrt 2 : ℝ) * (2 : ℝ) := by rw [show (Real.sqrt 2 : ℝ) ^2 = (2 : ℝ) by linarith [h5]]
          _ = (2 * (Real.sqrt 2 : ℝ)) := by ring
      nlinarith [h8, h5, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Case 3: x = -Real.sqrt 2
      rw [h_eq]
      have h5 : (Real.sqrt 2 : ℝ) ^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
      have eq3 : ((-Real.sqrt 2 : ℝ) ^3 + (-Real.sqrt 2 : ℝ)) / 3 = (-Real.sqrt 2 : ℝ) := by
        have h11 : (-Real.sqrt 2 : ℝ) ^3 = - (Real.sqrt 2 : ℝ) ^3 := by
          ring_nf
        have h12 : (Real.sqrt 2 : ℝ) ^3 = (2 * (Real.sqrt 2 : ℝ)) := by
          calc
            (Real.sqrt 2 : ℝ) ^3 = (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) ^2 := by ring
            _ = (Real.sqrt 2 : ℝ) * (2 : ℝ) := by rw [show (Real.sqrt 2 : ℝ) ^2 = (2 : ℝ) by linarith [h5]]
            _ = (2 * (Real.sqrt 2 : ℝ)) := by ring
        have h13 : (-Real.sqrt 2 : ℝ) ^3 + (-Real.sqrt 2 : ℝ) = (-3 * (Real.sqrt 2 : ℝ)) := by
          rw [h11]
          have h14 : - (Real.sqrt 2 : ℝ) ^3 = (-2 * (Real.sqrt 2 : ℝ)) := by
            linarith [h12]
          nlinarith [h14]
        have h14 : ((-Real.sqrt 2 : ℝ) ^3 + (-Real.sqrt 2 : ℝ)) / 3 = (-Real.sqrt 2 : ℝ) := by
          rw [h13]
          field_simp
          <;> nlinarith
        linarith
      rw [eq3]
      -- Now the goal is to show:
      -- (-Real.sqrt 2 : ℝ) ^3 + (-Real.sqrt 2 : ℝ) = 3 * (-Real.sqrt 2 : ℝ)
      have h8 : (-Real.sqrt 2 : ℝ) ^3 = (-2 * (Real.sqrt 2 : ℝ)) := by
        have h11 : (-Real.sqrt 2 : ℝ) ^3 = - (Real.sqrt 2 : ℝ) ^3 := by ring
        have h12 : (Real.sqrt 2 : ℝ) ^3 = (2 * (Real.sqrt 2 : ℝ)) := by
          calc
            (Real.sqrt 2 : ℝ) ^3 = (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) ^2 := by ring
            _ = (Real.sqrt 2 : ℝ) * (2 : ℝ) := by rw [show (Real.sqrt 2 : ℝ) ^2 = 2 by linarith [h5]]
            _ = (2 * (Real.sqrt 2 : ℝ)) := by ring
        rw [h11, h12]
        all_goals ring
      nlinarith [h8, h5, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]