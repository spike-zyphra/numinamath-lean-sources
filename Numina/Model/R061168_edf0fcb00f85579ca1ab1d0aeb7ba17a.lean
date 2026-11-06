import Mathlib

theorem algebra_321192 {x y : ℝ} (h1 : x^2 * y^2 + x^2 + y^2 = 9) (h2 : x^2 * y + x * y^2 - x - y = 3) :
    (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨ (x = -2 ∧ y = 1) ∨ (x = 1 ∧ y = -2) ∨
    (x = 0 ∧ y = -3) ∨ (x = -3 ∧ y = 0) := by

  have h3 : (x + y) * (x * y - 1) = 3 := by
    nlinarith [h2]

  have h4 : (x * y)^2 - 2 * (x * y) + (x + y)^2 = 9 := by
    nlinarith [h1]

  by_cases h5 : x * y - 1 = 0

  · -- case where x*y-1=0
    have h6 : x * y = 1 := by linarith

    nlinarith [h3, h6]

  · -- case where x*y-1≠0
    have h8 : (x + y) ^ 2 = 9 + 2 * (x * y) - (x * y) ^ 2 := by nlinarith [h1]

    have h10 : (x * y) * ((x * y) - 4) * ((x * y) - 2) * ((x * y) + 2) = 0 := by
      nlinarith [h3, h8, h5]

    cases' (mul_eq_zero.mp h10) with h11 h12
    cases' (mul_eq_zero.mp h11) with h13 h14
    cases' (mul_eq_zero.mp h13) with h15 h16

    · -- case where x * y = 0
      have h17 : x * y = 0 := by linarith

      have h18 : (x + y) = -3 := by
        nlinarith [h3, h17]

      cases' (mul_eq_zero.mp h17) with h19 h20

      · -- case where x = 0
        have hy : y = -3 := by linarith [h18, h19]

        have h21 : x = 0 := by linarith

        have h22 : (x = 0 ∧ y = -3) := ⟨h21, hy⟩

        tauto

      · -- case where y = 0
        have hx : x = -3 := by linarith [h18, h20]

        have h21 : y = 0 := by linarith

        have h22 : (x = -3 ∧ y = 0) := ⟨hx, h21⟩

        tauto

    · -- case where x * y - 4 = 0
      have h23 : x * y = 4 := by linarith

      have h24 : (x + y) = 1 := by
        nlinarith [h3, h23]

      nlinarith [sq_nonneg (x - y), h23, h24]

    · -- case where x * y - 2 = 0
      have h25 : x * y = 2 := by linarith

      have h26 : (x + y) = 3 := by
        nlinarith [h3, h25]

      have h27 : (x - 1) * (x - 2) = 0 := by
        nlinarith [h25, h26]

      cases' (mul_eq_zero.mp h27) with h28 h29

      · -- case where x = 1
        have hx : x = 1 := by linarith

        have hy : y = 2 := by linarith [h26, hx]

        have h30 : (x = 1 ∧ y = 2) := ⟨hx, hy⟩

        tauto

      · -- case where x = 2
        have hx : x = 2 := by linarith

        have hy : y = 1 := by linarith [h26, hx]

        have h31 : (x = 2 ∧ y = 1) := ⟨hx, hy⟩

        tauto

    · -- case where x * y + 2 = 0
      have h32 : x * y = -2 := by linarith

      have h33 : (x + y) = -1 := by
        nlinarith [h3, h32]

      have h34 : (x - 1) * (x + 2) = 0 := by
        nlinarith [h32, h33]

      cases' (mul_eq_zero.mp h34) with h35 h36

      · -- case where x = 1
        have hx : x = 1 := by linarith

        have hy : y = -2 := by linarith [h33, hx]

        have h37 : (x = 1 ∧ y = -2) := ⟨hx, hy⟩

        tauto

      · -- case where x = -2
        have hx : x = -2 := by linarith

        have hy : y = 1 := by linarith [h33, hx]

        have h38 : (x = -2 ∧ y = 1) := ⟨hx, hy⟩

        tauto