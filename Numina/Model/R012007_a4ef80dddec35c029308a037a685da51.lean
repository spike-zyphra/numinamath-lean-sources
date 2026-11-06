import Mathlib

theorem algebra_188099 (x y z : ℝ) :
    x^2 + y * z = y + z ∧ y^2 + x * z = x + z ∧ z^2 + x * y = x + y ↔
    (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 1 ∧ y = 1 ∧ z = 1) ∨ (x = -1 ∧ y = 1 ∧ z = 1) ∨ (x = 1 ∧ y = -1 ∧ z = 1) ∨ (x = 1 ∧ y = 1 ∧ z = -1) := by
  constructor
  · -- Forward implication: if (x, y, z) satisfies the system, then it's one of the given solutions.
    rintro ⟨h₁, h₂, h₃⟩
    have eq1 : (x - y) * (x + y - z + 1) = 0 := by
      nlinarith
    have eq2 : (y - z) * (y + z - x + 1) = 0 := by
      nlinarith
    have eq3 : (z - x) * (z + x - y + 1) = 0 := by
      nlinarith
    cases (mul_eq_zero.1 eq1) with
    | inl h4 =>
      have h4' : x = y := by linarith
      have eq2' : (y - z) * (z + 1) = 0 := by
        rw [show x = y by linarith] at eq2
        nlinarith
      cases (mul_eq_zero.1 eq2') with
      | inl h5 =>
        have h5' : y = z := by linarith
        have h7 : x = z := by
          linarith [h4', h5']
        have h8 : x * (x - 1) = 0 := by
          have h9 : x ^ 2 + y * z = y + z := by linarith [h₁]
          rw [show y = x by linarith [h4'], show z = x by linarith [h7]] at h9
          nlinarith
        cases (mul_eq_zero.1 h8) with
        | inl hx0 =>
          have hx0' : x = 0 := by nlinarith
          have hy0 : y = 0 := by linarith [h4', hx0']
          have hz0 : z = 0 := by linarith [h7, hx0']
          left
          exact ⟨hx0', hy0, hz0⟩
        | inr h10 =>
          have hx1 : x = 1 := by linarith
          have hy1 : y = 1 := by linarith [h4', hx1]
          have hz1 : z = 1 := by linarith [h7, hx1]
          right
          left
          exact ⟨hx1, hy1, hz1⟩
      | inr h6 =>
        have hz1 : z = -1 := by linarith
        have h12 : x = 1 := by
          have h9 : x ^ 2 + y * z = y + z := by linarith [h₁]
          rw [show y = x by linarith [h4'], show z = -1 by linarith [hz1]] at h9
          nlinarith
        have hy1 : y = 1 := by linarith [h4', h12]
        right
        right
        right
        right
        exact ⟨by linarith, by linarith, by linarith⟩
    | inr h4 =>
      have h10 : x + y - z + 1 = 0 := by linarith
      have h11 : (z - x) * (2 * (x + 1)) = 0 := by
        have h100 : y = z - 1 - x := by
          linarith [h10]
        rw [show y = z - 1 - x by linarith [h100]] at eq3
        nlinarith
      cases (mul_eq_zero.1 h11) with
      | inl h12 =>
        have h14 : z = x := by linarith
        have h15 : y = -1 := by
          nlinarith [h10, h14]
        have h16 : x = 1 := by
          have h9 : x ^ 2 + y * z = y + z := by linarith [h₁]
          rw [show y = -1 by linarith [h15], show z = x by linarith [h14]] at h9
          nlinarith [sq_nonneg (x - 1)]
        have h17 : x = 1 := by linarith
        have h18 : y = -1 := by linarith [h15]
        have h19 : z = 1 := by
          nlinarith [h14, h17]
        right
        right
        right
        left
        exact ⟨by linarith, by linarith, by linarith⟩
      | inr h13 =>
        have h14 : x + 1 = 0 := by
          nlinarith
        have h15 : x = -1 := by
          nlinarith
        have h16 : y = z := by
          nlinarith [h10, h15]
        have h17 : y = 1 := by
          have h9 : x ^ 2 + y * z = y + z := by linarith [h₁]
          rw [show x = -1 by linarith [h15], show z = y by linarith [h16]] at h9
          nlinarith [sq_nonneg (y - 1)]
        have h18 : z = 1 := by
          linarith [h16, h17]
        right
        right
        left
        exact ⟨by linarith, by linarith, by linarith⟩
  · -- Backward implication: each given solution satisfies the system.
    rintro (h | h | h | h | h)
    · -- (0, 0, 0)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · -- Check first equation
        norm_num
      constructor
      · -- Check second equation
        norm_num
      · -- Check third equation
        norm_num
    · -- (1, 1, 1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · -- Check first equation
        norm_num
      constructor
      · -- Check second equation
        norm_num
      · -- Check third equation
        norm_num
    · -- (-1, 1, 1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · -- Check first equation
        norm_num
      constructor
      · -- Check second equation
        norm_num
      · -- Check third equation
        norm_num
    · -- (1, -1, 1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · -- Check first equation
        norm_num
      constructor
      · -- Check second equation
        norm_num
      · -- Check third equation
        norm_num
    · -- (1, 1, -1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · -- Check first equation
        norm_num
      constructor
      · -- Check second equation
        norm_num
      · -- Check third equation
        norm_num