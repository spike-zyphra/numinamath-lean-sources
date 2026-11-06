import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_159165 {f : ℝ → ℝ}
  (hf : f = λ x => (x^4 - x^3 - x + 1) / (x^3 - 5 * x^2 + 7 * x - 3) * abs (x - 3)) :
  ∀ x, x < 1 ∨ x ∈ Ioo 1 3 → f x = -(x^2 + x + 1) ∧
  ∀ x, x > 3 → f x = x^2 + x + 1 := by
  intro x h
  rcases h with h | h
  · -- Case where x < 1:
    have h1 : x < 1 := h
    have h2 : abs (x - 3) = 3 - x := by
      rw [abs_of_neg]
      linarith
      all_goals linarith
    have h3 : x^3 - 5 * x^2 + 7 * x - 3 ≠ 0 := by
      by_contra h'
      have h4 : (x - 1)^2 * (x - 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h4) with h5 h6
      · -- h5: (x - 1)^2 = 0
        have h7 : x - 1 = 0 := by
          apply pow_eq_zero 
          exact h5
        have h8 : x = 1 := by linarith
        nlinarith
      · -- h6: x - 3 = 0
        have h7 : x = 3 := by linarith
        nlinarith
    have h10 : f x = (x^4 - x^3 - x + 1) / (x^3 - 5 * x^2 + 7 * x - 3) * abs (x - 3) := by
      rw [hf]
    rw [h10]
    have eq1 : x^3 - 5*x^2 + 7*x - 3 = (x - 1)^2 * (x - 3) := by
      ring_nf
    have eq2 : x^4 - x^3 - x + 1 = (x^2 + x + 1) * (x - 1)^2 := by
      ring_nf
    have h8 : x - 1 ≠ 0 := by
      by_contra h9
      have h10 : x = 1 := by linarith
      nlinarith
    have h9 : x - 3 ≠ 0 := by
      by_contra h10
      have h11 : x = 3 := by nlinarith
      nlinarith
    have eq3 : (x^4 - x^3 - x + 1) / (x^3 - 5 * x^2 + 7 * x - 3) = (x^2 + x + 1) / (x - 3) := by 
      rw [eq1, eq2]
      field_simp [(show (x - 1) ≠ 0 by assumption), (show (x - 3) ≠ 0 by assumption)]
      <;> ring
    rw [eq3, h2]
    constructor
    · -- Show f x = -(x^2 + x + 1):
      have eq4 : (x^2 + x + 1) / (x - 3) * (3 - x) = -(x^2 + x + 1) := by 
        have h10 : x - 3 ≠ 0 := by
          by_contra h11
          have h12 : x = 3 := by linarith
          nlinarith
        field_simp [h10]
        <;> ring
      linarith [eq4]
    · -- Show ∀ x, x > 3 → f x = x^2 + x + 1:
      intro y hy
      have eq1 : abs (y - 3) = y - 3 := by
        rw [abs_of_pos]
        nlinarith
      have eq4 : f y = (y^4 - y^3 - y + 1) / (y^3 - 5 * y^2 + 7 * y - 3) * abs (y - 3) := by
        rw [hf]
      rw [eq4]
      have h7 : y^3 - 5 * y^2 + 7 * y - 3 ≠ 0 := by
        by_contra h'
        have h4 : (y - 1)^2 * (y - 3) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h4) with h5 h6
        · -- h5: (y - 1)^2 = 0
          have h7 : y - 1 = 0 := by
            apply pow_eq_zero 
            exact h5
          have h8 : y = 1 := by linarith
          nlinarith
        · -- h6: y - 3 = 0
          have h7 : y = 3 := by linarith
          nlinarith
      have eq3 : (y^4 - y^3 - y + 1) / (y^3 - 5 * y^2 + 7 * y - 3) = (y^2 + y + 1) / (y - 3) := by 
        have eq1 : y^3 - 5*y^2 + 7*y - 3 = (y - 1)^2 * (y - 3) := by
          ring_nf
        have eq2 : y^4 - y^3 - y + 1 = (y^2 + y + 1) * (y - 1)^2 := by
          ring_nf
        rw [eq1, eq2]
        have h8 : y - 1 ≠ 0 := by
          by_contra h9
          have h10 : y = 1 := by linarith
          nlinarith
        have h9 : y - 3 ≠ 0 := by
          by_contra h10
          have h11 : y = 3 := by nlinarith
          nlinarith
        field_simp [(show (y - 1) ≠ 0 by assumption), (show (y - 3) ≠ 0 by assumption)]
        <;> ring
      rw [eq3, eq1]
      have h11 : y - 3 ≠ 0 := by
        by_contra h12
        have h13 : y = 3 := by nlinarith
        nlinarith
      have eq2 : (y^2 + y + 1) / (y - 3) * (y - 3) = y^2 + y + 1 := by
        field_simp [h11]
        <;> ring
      linarith [eq2]
  · -- Case where x ∈ Ioo 1 3:
    rcases h with ⟨h1, h2⟩
    have h3 : abs (x - 3) = 3 - x := by
      rw [abs_of_neg]
      linarith
      all_goals linarith
    have h4 : x^3 - 5 * x^2 + 7 * x - 3 ≠ 0 := by
      by_contra h'
      have h4 : (x - 1)^2 * (x - 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h4) with h5 h6
      · -- h5: (x - 1)^2 = 0
        have h7 : x - 1 = 0 := by
          apply pow_eq_zero 
          exact h5
        have h8 : x = 1 := by linarith
        linarith
      · -- h6: x - 3 = 0
        have h7 : x = 3 := by linarith
        linarith
    have h10 : f x = (x^4 - x^3 - x + 1) / (x^3 - 5 * x^2 + 7 * x - 3) * abs (x - 3) := by
      rw [hf]
    rw [h10]
    have eq1 : x^3 - 5*x^2 + 7*x - 3 = (x - 1)^2 * (x - 3) := by
      ring_nf
    have eq2 : x^4 - x^3 - x + 1 = (x^2 + x + 1) * (x - 1)^2 := by
      ring_nf
    have h8 : x - 1 ≠ 0 := by
      by_contra h9
      have h10 : x = 1 := by linarith
      linarith
    have h9 : x - 3 ≠ 0 := by
      by_contra h10
      have h11 : x = 3 := by linarith
      linarith
    have eq3 : (x^4 - x^3 - x + 1) / (x^3 - 5 * x^2 + 7 * x - 3) = (x^2 + x + 1) / (x - 3) := by 
      rw [eq1, eq2]
      field_simp [(show (x - 1) ≠ 0 by assumption), (show (x - 3) ≠ 0 by assumption)]
      <;> ring
    rw [eq3, h3]
    constructor
    · -- Show f x = -(x^2 + x + 1):
      have eq4 : (x^2 + x + 1) / (x - 3) * (3 - x) = -(x^2 + x + 1) := by 
        have h10 : x - 3 ≠ 0 := by
          by_contra h11
          have h12 : x = 3 := by linarith
          nlinarith
        field_simp [h10]
        <;> ring
      linarith [eq4]
    · -- Show ∀ x, x > 3 → f x = x^2 + x + 1:
      intro y hy
      have eq1 : abs (y - 3) = y - 3 := by
        rw [abs_of_pos]
        nlinarith
      have eq4 : f y = (y^4 - y^3 - y + 1) / (y^3 - 5 * y^2 + 7 * y - 3) * abs (y - 3) := by
        rw [hf]
      rw [eq4]
      have h7 : y^3 - 5 * y^2 + 7 * y - 3 ≠ 0 := by
        by_contra h'
        have h4 : (y - 1)^2 * (y - 3) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h4) with h5 h6
        · -- h5: (y - 1)^2 = 0
          have h7 : y - 1 = 0 := by
            apply pow_eq_zero 
            exact h5
          have h8 : y = 1 := by linarith
          nlinarith
        · -- h6: y - 3 = 0
          have h7 : y = 3 := by linarith
          nlinarith
      have eq3 : (y^4 - y^3 - y + 1) / (y^3 - 5 * y^2 + 7 * y - 3) = (y^2 + y + 1) / (y - 3) := by 
        have eq1 : y^3 - 5*y^2 + 7*y - 3 = (y - 1)^2 * (y - 3) := by
          ring_nf
        have eq2 : y^4 - y^3 - y + 1 = (y^2 + y + 1) * (y - 1)^2 := by
          ring_nf
        rw [eq1, eq2]
        have h8 : y - 1 ≠ 0 := by
          by_contra h9
          have h10 : y = 1 := by linarith
          nlinarith
        have h9 : y - 3 ≠ 0 := by
          by_contra h10
          have h11 : y = 3 := by nlinarith
          nlinarith
        field_simp [(show (y - 1) ≠ 0 by assumption), (show (y - 3) ≠ 0 by assumption)]
        <;> ring
      rw [eq3, eq1]
      have h11 : y - 3 ≠ 0 := by
        by_contra h12
        have h13 : y = 3 := by nlinarith
        nlinarith
      have eq2 : (y^2 + y + 1) / (y - 3) * (y - 3) = y^2 + y + 1 := by
        field_simp [h11]
        <;> ring
      linarith [eq2]