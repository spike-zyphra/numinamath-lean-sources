import Mathlib

/-if a,b and c are non-zero real numbers, and a+b+c=abc=a^3, then the minimum value of ab+bc+ca is ?-/
theorem algebra_306011 : IsLeast {x : ℝ | ∃ a b c : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a + b + c = a * b * c ∧ a * b * c = a ^ 3 ∧ x = a * b + b * c + c * a} 9 := by

  constructor
  · -- We'll prove 9 belongs to the set by choosing specific values for a, b, c
    use Real.sqrt 3, Real.sqrt 3, Real.sqrt 3
    constructor
    · -- Show a ≠ 0
      positivity
    constructor
    · -- Show b ≠ 0
      positivity
    constructor
    · -- Show c ≠ 0
      positivity
    constructor
    · -- Show a + b + c = a * b * c
      have h1 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > (0 : ℝ))]
    constructor
    · -- Show a * b * c = a ^ 3
      have h1 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > (0 : ℝ))]
    · -- Show x = a * b + b * c + c * a
      ring_nf
      have o: √3 ^ 2 = 3 := by
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        norm_num
        apply Real.sqrt_nonneg
      simp [o]
      norm_num

  · -- Now prove that 9 is a lower bound
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, h2, h3⟩
    have hbc : b * c = a ^ 2 := by
      have hne : a ≠ 0 := ha
      have eq1 : a * (b * c) = a ^ 3 := by linarith
      have eq2 : b * c = a ^ 2 := by
        apply (mul_left_inj' hne).mp
        linarith
      exact eq2
    have h4 : a ^ 2 ≥ 3 := by
      have h5 : (b - c) ^ 2 ≥ 0 := sq_nonneg (b - c)
      have h6 : (b + c) ^ 2 - 4 * (b * c) ≥ 0 := by
        nlinarith [sq_nonneg (b - c)]
      have h7 : (b + c) ^ 2 - 4 * (b * c) = (a ^ 3 - a) ^ 2 - 4 * (a ^ 2) := by
        have hbc2 : b + c = a ^ 3 - a := by
          have hsum : a + b + c = a ^ 3 := by
            nlinarith [h1, h2]
          linarith
        rw [hbc2, hbc]
      rw [h7] at h6
      have h8 : (a ^ 3 - a) ^ 2 - 4 * (a ^ 2) = a^6 - 2 * a^4 - 3 * a^2 := by
        ring
      rw [h8] at h6
      have h9 : a^6 - 2 * a^4 - 3 * a^2 ≥ 0 := by linarith
      have h10 : a^2 * (a^4 - 2 * a^2 - 3) ≥ 0 := by
        nlinarith [sq_nonneg (a^2), sq_nonneg (a^3 - a), h9]
      have h11 : a^2 > 0 := by
        exact sq_pos_of_ne_zero ha
      have h12 : a^4 - 2 * a^2 - 3 ≥ 0 := by
        nlinarith [h10, h11]
      have h13 : (a^2 - 3) * (a^2 + 1) ≥ 0 := by
        nlinarith [sq_nonneg (a^2), sq_nonneg (a), h12]
      have h14 : a^2 - 3 ≥ 0 := by
        nlinarith [sq_nonneg (a^2 - 3), sq_nonneg (a^2 + 1), h13]
      linarith
    have h5 : x = a^4 := by
      have eq1 : x = a * b + b * c + c * a := by linarith
      have eq2 : a * b + b * c + c * a = a^4 := by
        have hbc_eq : b * c = a ^ 2 := hbc
        have eq_b_sum : b + c = a^3 - a := by
          have hsum : a + b + c = a ^ 3 := by linarith [h1, h2]
          linarith
        have eq1 : a * b + b * c + c * a = a * (b + c) + b * c := by ring
        rw [eq1]
        rw [eq_b_sum, hbc_eq]
        ring
      linarith [eq2]
    have h6 : a^4 ≥ 9 := by
      have h7 : a^2 ≥ 3 := h4
      nlinarith [sq_nonneg (a^2 - 3), h7]
    linarith [h5, h6]