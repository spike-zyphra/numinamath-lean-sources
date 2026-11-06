import Mathlib

open Real Int Nat

theorem algebra_324708 {x y : ℝ} (hx : ⌊Real.sqrt x⌋ = 9) (hy : ⌊Real.sqrt y⌋ = 12) :
    ⌊x + y⌋ ≤ 268 := by
  have h1 : 9 ≤ Real.sqrt x := by
    have h1 : (⌊Real.sqrt x⌋ : ℝ) ≤ Real.sqrt x := Int.floor_le (Real.sqrt x)
    have h2 : (⌊Real.sqrt x⌋ : ℝ) = 9 := by exact_mod_cast hx
    linarith

  have h2 : Real.sqrt x < 10 := by
    have h3 : Real.sqrt x < (⌊Real.sqrt x⌋ + 1 : ℝ) := Int.lt_floor_add_one (Real.sqrt x)
    have h4 : (⌊Real.sqrt x⌋ + 1 : ℝ) = 10 := by
      have h5 : (⌊Real.sqrt x⌋ : ℝ) = 9 := by exact_mod_cast hx
      linarith
    linarith

  have h3 : 12 ≤ Real.sqrt y := by
    have h1 : (⌊Real.sqrt y⌋ : ℝ) ≤ Real.sqrt y := Int.floor_le (Real.sqrt y)
    have h2 : (⌊Real.sqrt y⌋ : ℝ) = 12 := by exact_mod_cast hy
    linarith

  have h4 : Real.sqrt y < 13 := by
    have h3 : Real.sqrt y < (⌊Real.sqrt y⌋ + 1 : ℝ) := Int.lt_floor_add_one (Real.sqrt y)
    have h4 : (⌊Real.sqrt y⌋ + 1 : ℝ) = 13 := by
      have h2 : (⌊Real.sqrt y⌋ : ℝ) = 12 := by exact_mod_cast hy
      linarith
    linarith

  have h5'1 : 81 ≤ x := by
    have h6 : (9 : ℝ) ≤ Real.sqrt x := h1
    have h7 : 0 ≤ Real.sqrt x := by positivity
    have h77 : Real.sqrt x ^ 2 ≥ (9 : ℝ) ^ 2 := by nlinarith [Real.sqrt_nonneg x, h6]
    have h88 : Real.sqrt x ^ 2 = x := by
      have h_nonneg : 0 ≤ x := by
        by_contra h
        push_neg at h
        have h10 : Real.sqrt x = 0 := by
          rw [Real.sqrt_eq_zero']
          nlinarith
        linarith [h1, h10, Real.sqrt_nonneg x]
      have h_sq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
      linarith
    nlinarith

  have h6 : x < 100 := by
    have h10 : (Real.sqrt x) < (10 : ℝ) := h2
    have h11 : Real.sqrt x ^ 2 < (10 : ℝ) ^ 2 := by nlinarith [Real.sqrt_nonneg x, h10]
    have h80 : Real.sqrt x ^ 2 = x := by
      have h_nonneg : 0 ≤ x := by
        by_contra h
        push_neg at h
        have h10 : Real.sqrt x = 0 := by
          rw [Real.sqrt_eq_zero']
          nlinarith
        linarith [h1, h10, Real.sqrt_nonneg x]
      have h_sq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
      linarith
    nlinarith

  have h7'1 : 144 ≤ y := by
    have h112 : (12 : ℝ) ≤ Real.sqrt y := h3
    have h113 : 0 ≤ Real.sqrt y := by positivity
    have h7777 : Real.sqrt y ^ 2 ≥ (12 : ℝ) ^ 2 := by nlinarith [Real.sqrt_nonneg y, h112]
    have h7778 : Real.sqrt y ^ 2 = y := by
      have h_nonneg : 0 ≤ y := by
        by_contra h
        push_neg at h
        have h110 : Real.sqrt y = 0 := by
          rw [Real.sqrt_eq_zero']
          nlinarith
        linarith [h3, h110, Real.sqrt_nonneg y]
      have h_sq : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
      linarith
    nlinarith

  have h8 : y < 169 := by
    have h44 : (Real.sqrt y) < (13 : ℝ) := h4
    have h45 : Real.sqrt y ^ 2 < (13 : ℝ) ^ 2 := by nlinarith [Real.sqrt_nonneg y, h44]
    have h7779 : Real.sqrt y ^ 2 = y := by
      have h_nonneg : 0 ≤ y := by
        by_contra h
        push_neg at h
        have h110 : Real.sqrt y = 0 := by
          rw [Real.sqrt_eq_zero']
          nlinarith
        linarith [h3, h110, Real.sqrt_nonneg y]
      have h_sq : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
      linarith
    nlinarith

  have h9 : x + y < 269 := by
    nlinarith

  have h10 : ⌊x + y⌋ ≤ 268 := by
    have h11 : x + y < 269 := h9
    have h12 : ⌊x + y⌋ ≤ 268 := by
      by_contra h
      push_neg at h
      have : (269 : ℝ) ≤ x + y := by
        have h13 : (⌊x + y⌋ : ℝ) ≤ x + y := Int.floor_le (x + y)
        have h14 : (⌊x + y⌋ : ℝ) ≥ (269 : ℝ) := by
          have h15 : ⌊x + y⌋ ≥ 269 := by
            linarith
          exact_mod_cast h15
        linarith
      linarith
    exact_mod_cast h12

  exact_mod_cast h10