import Mathlib

theorem number_theory_154008 :
    {(x, y) : ℤ × ℤ | x^3 = y^3 + 2 * y^2 + 1} = {(1, 0), (1, -2), (-2, -3)} := by

  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) satisfies the equation, prove (x, y) ∈ {(1, 0), (1, -2), (-2, -3)}
    rintro H
    have eq1 : x^3 = y^3 + 2 * y^2 + 1 := by
      linarith

    have h1 : x > y := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y + 1), sq_nonneg (x - y - 1), sq_nonneg (x + 2), sq_nonneg (y + 2)]

    have h2 : x - y ≤ 3 := by
      nlinarith [sq_nonneg (x - y - 3), sq_nonneg (x + 2), sq_nonneg (y + 2), sq_nonneg (x - y - 1), sq_nonneg (x - y - 2), sq_nonneg (y + 3), sq_nonneg (x - y), sq_nonneg (x - y - 3), sq_nonneg (x + y)]

    have h3 : x - y = 1 ∨ x - y = 2 ∨ x - y = 3 := by
      omega
    rcases h3 with h | h | h
    · -- Case x - y = 1.
      have h4 : x = y + 1 := by linarith
      rw [h4] at eq1
      have eq2 : (y + 1: ℤ)^3 = y^3 + 2 * y^2 + 1 := eq1
      have eq3 : y * (y + 3) = 0 := by
        ring_nf at eq2
        nlinarith
      have eq4 : y = 0 ∨ y = -3 := by
        cases (mul_eq_zero.mp eq3) with
        | inl h5 => 
          left
          linarith
        | inr h6 => 
          right
          linarith
      rcases eq4 with h5 | h6
      · -- Case y = 0.
        have h0 : y = 0 := h5
        have hx : x = 1 := by 
          linarith [h4, h0]
        simp [hx, h0]
      · -- Case y = -3.
        have h0 : y = -3 := h6
        have hx : x = -2 := by 
          linarith [h4, h0]
        simp [hx, h0]
    · -- Case x - y = 2.
      have h4 : x = y + 2 := by linarith
      rw [h4] at eq1
      ring_nf at eq1
      exfalso
      have h4 : 4 * y^2 + 12 * y + 7 = 0 := by nlinarith
      have h5 : y ≥ -2 := by nlinarith [sq_nonneg (4 * y + 6)]
      have h6 : y ≤ -1 := by nlinarith [sq_nonneg (4 * y + 6)]
      interval_cases y <;> omega
    · -- Case x - y = 3.
      have h4 : x = y + 3 := by linarith
      rw [h4] at eq1
      ring_nf at eq1
      have eq3 : 7 * y^2 + 27 * y + 26 = 0 := by 
        nlinarith
      have h6 : y = -2 := by
        nlinarith [sq_nonneg (y + 2), sq_nonneg (7 * y + 14)]
      have h1x : x = 1 := by
        linarith [h4, h6]
      simp [h1x, h6]
  · -- Show the given solutions satisfy the equation
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check (1, 0)
      norm_num
    · -- Check (1, -2)
      norm_num
    · -- Check (-2, -3)
      norm_num