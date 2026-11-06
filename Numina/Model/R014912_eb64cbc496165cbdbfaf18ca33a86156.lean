import Mathlib

theorem algebra_317730 :
    IsLeast {x | ∃ a b : ℝ, x = a^2 + b^2 ∧ ∃ y : ℝ, y^4 + a * y^3 + b * y^2 + a * y + 1 = 0} (4 / 5) := by
  constructor
  · -- Show 4/5 in the set
    use -4 / 5, -2 / 5
    constructor
    · -- Show a^2 + b^2 = 4/5
      norm_num
    · -- Show exists real root
      use 1
      norm_num
  · -- Show 4/5 is minimal
    intro x hx
    rcases hx with ⟨a, b, hx_eq, y, hy⟩
    have h1 : y ≠ 0 := by
      by_contra h
      rw [h] at hy
      nlinarith
    have h2 : y ^ 2 + a * y + b + a / y + 1 / y ^ 2 = 0 := by
      have hne : y ≠ 0 := h1
      have h1 : y^2 ≠ 0 := by
        intro h2
        apply hne
        nlinarith [sq_nonneg y, h2]
      have h_eq : y^4 + a*y^3 + b*y^2 + a*y + 1 = 
                  y^2 * (y^2 + a*y + b + a/y + 1/y^2) := by
        field_simp [hne]
        ring
      rw [h_eq] at hy
      have h2 : y^2 * (y^2 + a*y + b + a/y + 1/y^2) = 0 := hy
      have h3 : y^2 + a*y + b + a/y + 1/y^2 = 0 := by
        apply (mul_eq_zero.mp h2).resolve_left
        exact h1
      exact h3
    -- now h2 holds.

    have ht_eq : (y + 1 / y) ^ 2 + a * (y + 1 / y) + (b - 2) = 0 := by
      have hne : y ≠ 0 := h1
      have eq1 : y ^ 2 + a * y + b + a / y + 1 / y ^ 2 = 0 := h2
      have eq2 : (y + 1 / y) ^ 2 = y ^ 2 + 2 + 1 / y ^ 2 := by 
        field_simp [hne]
        <;> ring
      have h3 : (y + 1 / y) ^ 2 + a * (y + 1 / y) + (b - 2) = y ^ 2 + 1 / y ^ 2 + a * y + a / y + b := by
        have hne : y ≠ 0 := h1
        field_simp [hne]
        <;> ring
      have h4 : y ^ 2 + 1 / y ^ 2 + a * y + a / y + b = 0 := by
        have eq1' : y ^ 2 + a * y + b + a / y + 1 / y ^ 2 = 0 := eq1
        have h5 : y ^ 2 + a * y + b + a / y + 1 / y ^ 2 = y ^ 2 + 1 / y ^ 2 + a * y + a / y + b := by 
          field_simp [hne]
          <;> ring
        linarith [h5, eq1']
      rw [h3]
      exact h4
    have ht_sq : (y + 1 / y) ^ 2 ≥ 4 := by
      have hne : y ≠ 0 := h1
      have mx : (y + 1 / y) ^ 2 ≥ 4 := by
        have hy1 : y ≠ 0 := hne
        have h1 : (y + 1 / y) ^ 2 - 4 ≥ 0 := by
          have h2 : (y + 1 / y) ^ 2 - 4 = (y - 1 / y) ^ 2 := by 
            field_simp [hne]
            <;> nlinarith 
          have h3 : (y - 1 / y) ^ 2 ≥ 0 := sq_nonneg (y - 1 / y)
          linarith [h2, h3]
        linarith
      linarith

    have h3 : a ^ 2 + b ^ 2 ≥ 4 / 5 := by 
      nlinarith [ht_eq, ht_sq, sq_nonneg (a + 4 / 5), sq_nonneg (b + 2 / 5), sq_nonneg (y - 1), sq_nonneg (y + 1)]
    linarith [hx_eq, h3]