import Mathlib

theorem algebra_225927 (x y z : ℝ) :
    x + y - z = -1 ∧ x^2 - y^2 + z^2 = 1 ∧ -x^3 + y^3 + z^3 = -1 ↔
    (x = 1 ∧ y = -1 ∧ z = 1) ∨ (x = -1 ∧ y = -1 ∧ z = -1) := by
  constructor
  · -- Forward direction: if the equations are satisfied, then (x,y,z) is one of the solutions
    rintro ⟨h1, h2, h3⟩
    have h4 : z = x + y + 1 := by linarith
    rw [h4] at h2
    have h5 : (x + y) * (x + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case 1: x + y = 0
      have h8 : y = -x := by linarith
      have h9 : z = 1 := by
        rw [h8] at h4
        nlinarith
      rw [h8, h9] at h3
      have h10 : x = 1 := by
        have h11 : x^3 = 1 := by
          nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x - 1), sq_nonneg (x + 1)]
        have h12 : x = 1 := by
          have h13 : x^3 - 1 = 0 := by linarith
          have h14 : (x - 1) * (x^2 + x + 1) = 0 := by
            ring_nf at h13 ⊢
            linarith
          cases' (mul_eq_zero.mp h14) with h15 h16
          · -- Case where x - 1 = 0
            linarith
          · -- Case where x^2 + x + 1 = 0
            nlinarith [sq_nonneg (x + 1 / 2)]
        linarith
      have h13 : y = -1 := by
        linarith [h8, h10]
      have h14 : z = 1 := by
        linarith [h9]
      left
      exact ⟨h10, h13, h14⟩
    · -- Case 2: x + 1 = 0
      have h18 : x = -1 := by linarith
      have h19 : z = y := by
        rw [h18] at h4
        linarith
      rw [h18, show z = y by linarith [h19] ] at h3
      have h20 : y = -1 := by
        have h21 : y^3 = -1 := by
          nlinarith [sq_nonneg (y^2 + 1), sq_nonneg (y + 1), sq_nonneg (y - 1)]
        have h22 : y = -1 := by
          have h23 : y^3 + 1 = 0 := by
            linarith
          have h24 : (y + 1) * (y^2 - y + 1) = 0 := by
            ring_nf at h23 ⊢
            linarith
          cases' (mul_eq_zero.mp h24) with h25 h26
          · -- Case where y + 1 = 0
            linarith
          · -- Case where y^2 - y + 1 = 0
            nlinarith [sq_nonneg (y - 1 / 2)]
        linarith
      have h23 : z = -1 := by
        linarith [h19, h20]
      right
      exact ⟨by linarith, by linarith, by linarith⟩
  · -- Backward direction: if the solutions are as given, then they satisfy the equations
    rintro (h | h)
    · -- Case 1
      rcases h with ⟨r1, r2, r3⟩
      constructor
      · -- First equation
        rw [r1, r2, r3]
        norm_num
      constructor
      · -- Second equation
        rw [r1, r2, r3]
        norm_num
      · -- Third equation
        rw [r1, r2, r3]
        norm_num
    · -- Case 2
      rcases h with ⟨r1, r2, r3⟩
      constructor
      · -- First equation
        rw [r1, r2, r3]
        norm_num
      constructor
      · -- Second equation
        rw [r1, r2, r3]
        norm_num
      · -- Third equation
        rw [r1, r2, r3]
        norm_num