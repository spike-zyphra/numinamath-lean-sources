import Mathlib
/- let x,y and a be real nnumbers. And satisfy x +y = x^3+y^3=x^5+y^5 =a . Find all possible values of a-/
theorem algebra_320940 (x y a : ℝ) (h₀ : x + y = a) (h₁ : x^3 + y^3 = a) (h₂ : x^5 + y^5 = a) :
    a = -2 ∨ a = -1 ∨ a = 0 ∨ a = 1 ∨ a = 2 := by
  have h3 : (x + y) ^ 2 = x^2 + 2 * x * y + y^2 := by ring
  have h4 : x^3 + y^3 = (x + y) * (x^2 - x * y + y^2) := by ring
  have h5 : x^5 + y^5 = (x + y) * (x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4) := by ring
  by_cases ha : a = 0
  · -- If a = 0, then x + y = 0, so y = -x
    right
    right
    left
    exact ha
  · -- If a ≠ 0, we can derive more constraints
    have h6 : x^2 - x * y + y^2 = 1 := by
      have h7 : x^3 + y^3 = (x + y) * (x^2 - x * y + y^2) := by ring
      rw [h₀] at h7
      have h8 : a * (x^2 - x * y + y^2) = a := by linarith [h₁, h7]
      have h9 : x^2 - x * y + y^2 = 1 := by
        apply (mul_left_inj' ha).mp
        linarith
      exact h9
    have h10 : x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4 = 1 := by
      have h11 : x^5 + y^5 = (x + y) * (x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4) := by ring
      rw [h₀] at h11
      have h12 : a * (x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4) = a := by linarith [h₂, h11]
      have h13 : x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4 = 1 := by
        apply (mul_left_inj' ha).mp
        linarith
      exact h13
    have h14 : x * y = (a^2 - 1) / 3 := by
      have h15 : x^3 + y^3 = (x + y) ^ 3 - 3 * (x + y) * (x * y) := by ring
      rw [h₀] at h15
      have h16 : a^3 - 3 * a * (x * y) = a := by linarith [h₁, h15]
      have h17 : a^2 - 3 * (x * y) = 1 := by
        have h18 : a ≠ 0 := by
          intro h
          apply ha
          linarith
        apply (mul_left_inj' h18).mp
        nlinarith
      have h19 : x * y = (a^2 - 1) / 3 := by
        linarith
      exact h19
    have h20 : (x^2 + y^2) = (a^2 + 2) / 3 := by
      have h21 : x^2 + y^2 = (x + y) ^ 2 - 2 * (x * y) := by ring
      rw [h₀, h14] at h21
      linarith
    have h22 : x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4 = (-a^4 + 5 * a^2 + 5) / 9 := by
      have h23 : x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4 = (x^4 + y^4) - (x * y) * (x^2 + y^2) + (x * y) ^ 2 := by ring
      rw [h23]
      have h24 : x^4 + y^4 = (x^2 + y^2) ^ 2 - 2 * (x * y) ^ 2 := by ring
      rw [h24, h20, h14]
      have h25 : (x * y) * (x^2 + y^2) = (a^2 - 1) / 3 * ((a^2 + 2) / 3) := by
        rw [h14, h20]
      have h26 : (x * y) ^ 2 = ((a^2 - 1) / 3) ^ 2 := by
        rw [h14]
      nlinarith
    have h27 : (-a^4 + 5 * a^2 + 5) / 9 = 1 := by
      nlinarith [h10, h22]
    have h28 : -a^4 + 5 * a^2 - 4 = 0 := by
      nlinarith
    have h29 : a^4 - 5 * a^2 + 4 = 0 := by
      nlinarith
    have h30 : (a^2 - 4) * (a^2 - 1) = 0 := by
      ring_nf at h29 ⊢
      linarith
    cases' (mul_eq_zero.mp h30) with h31 h32
    · -- case a^2 - 4 = 0, so a^2 = 4, thus a = ±2
      have h33 : a^2 = 4 := by linarith
      have h34 : a = 2 ∨ a = -2 := by
        have h35 : a^2 - 4 = 0 := by linarith
        have h36 : (a - 2) * (a + 2) = 0 := by
          linarith
        cases' (mul_eq_zero.mp h36) with h37 h38
        · -- a - 2 = 0
          left
          linarith
        · -- a + 2 = 0
          right
          linarith
      cases' h34 with h47 h48
      · -- a = 2
        right
        right
        right
        right
        exact h47
      · -- a = -2
        left
        exact h48
    · -- case a^2 - 1 = 0, so a^2 = 1, thus a = ±1
      have h39 : a^2 = 1 := by linarith
      have h40 : a = 1 ∨ a = -1 := by
        have h41 : a^2 - 1 = 0 := by linarith
        have h42 : (a - 1) * (a + 1) = 0 := by
          linarith
        cases' (mul_eq_zero.mp h42) with h43 h44
        · -- a - 1 = 0
          left
          linarith
        · -- a + 1 = 0
          right
          linarith
      cases' h40 with h45 h46
      · -- a = 1
        right
        right
        right
        left
        exact h45
      · -- a = -1
        right
        left
        exact h46