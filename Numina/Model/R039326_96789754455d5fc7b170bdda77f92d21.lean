import Mathlib

theorem algebra_263529 {b : ℝ} (hb : b > 1) {x : ℝ} (hx : x > 0)
    (h : (2 * x) ^ Real.logb b 2 - (3 * x) ^ Real.logb b 3 = 0) :
    x = 1 / 6 := by

  have h1 : (2 * x) ^ Real.logb b 2 = (3 * x) ^ Real.logb b 3 := by linarith

  -- Taking logarithm of both sides
  have h2 : Real.log ((2 * x) ^ Real.logb b 2) = Real.log ((3 * x) ^ Real.logb b 3) := by
    rw [h1]

  -- Applying logarithm property: ln(a^c) = c * ln(a)
  have h3 : Real.log ((2 * x) ^ Real.logb b 2) = Real.logb b 2 * Real.log (2 * x) := by
    rw [Real.log_rpow]
    all_goals nlinarith

  have h4 : Real.log ((3 * x) ^ Real.logb b 3) = Real.logb b 3 * Real.log (3 * x) := by
    rw [Real.log_rpow]
    all_goals nlinarith

  -- Substituting h3 and h4 into h2
  rw [h3, h4] at h2

  -- Convert logarithm base using Real.logb b a = Real.log a / Real.log b
  have h5 : Real.logb b 2 = Real.log 2 / Real.log b := by
    field_simp [Real.logb]

  have h6 : Real.logb b 3 = Real.log 3 / Real.log b := by
    field_simp [Real.logb]

  -- Substituting base conversion expressions into the equation
  rw [h5] at h2
  rw [h6] at h2

  -- Multiply both sides by Real.log b, which is positive since b > 1
  have h7 : Real.log b > 0 := by
    apply Real.log_pos
    linarith

  have h8 : Real.log 2 * Real.log (2 * x) = Real.log 3 * Real.log (3 * x) := by
    have h9 : Real.log b > 0 := h7
    field_simp at h2 ⊢
    nlinarith

  -- Expanding Real.log(2 * x) and Real.log(3 * x) using logarithm properties
  have h9 : Real.log (2 * x) = Real.log 2 + Real.log x := by
    rw [Real.log_mul (by norm_num) (by linarith)]

  have h10 : Real.log (3 * x) = Real.log 3 + Real.log x := by
    rw [Real.log_mul (by norm_num) (by linarith)]

  -- Substitute expanded expressions into h8
  rw [h9] at h8
  rw [h10] at h8

  -- Rearranging the equation to factor
  have h12 : (Real.log 2 - Real.log 3) * (Real.log 2 + Real.log 3 + Real.log x) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h12) with h13 h14
  · -- Case where Real.log 2 - Real.log 3 = 0
    exfalso
    have h15 : Real.log 2 = Real.log 3 := by linarith
    have h16 : (2 : ℝ) = 3 := by
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by norm_num : (2 : ℝ) > 0)) (Set.mem_Ioi.mpr ( by norm_num : (3 : ℝ) > 0)) h15
    linarith

  · -- Case where Real.log 2 + Real.log 3 + Real.log x = 0
    have h17 : Real.log 2 + Real.log 3 + Real.log x = 0 := by
      linarith [h14]

    -- Simplify Real.log 2 + Real.log 3 = Real.log 6
    have h18 : Real.log 2 + Real.log 3 = Real.log 6 := by
      calc
        Real.log 2 + Real.log 3 = Real.log (2 * 3) := by rw [Real.log_mul (by norm_num) (by norm_num)]
        _ = Real.log 6 := by norm_num

    have h19 : Real.log 6 + Real.log x = 0 := by
      linarith [h18, h17]

    -- Combine logarithms: Real.log 6 + Real.log x = Real.log (6 * x)
    have h20 : Real.log (6 * x) = 0 := by
      have h19' : Real.log (6 * x) = Real.log 6 + Real.log x := by
        rw [Real.log_mul (by norm_num) (by linarith)]
      linarith [h19', h19]

    -- Real.log (6 * x) = 0 implies 6 * x = 1
    have h21 : 6 * x = 1 := by
      have h22 : 6 * x > 0 := by nlinarith
      have h23 : Real.log (6 * x) = 0 := h20
      have h24 : 6 * x = 1 := by
        rw [Real.log_eq_zero] at h23
        rcases h23 with (r | r | r)
        · linarith
        · linarith
        · linarith
      exact h24

    -- Solve for x: 6 * x = 1 implies x = 1/6
    linarith