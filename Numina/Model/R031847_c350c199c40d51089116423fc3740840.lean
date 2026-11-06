import Mathlib

theorem algebra_166079 (x y z : ℝ) (h₀ : x + y * z = 2) (h₁ : y + z * x = 2) (h₂ : z + x * y = 2) :
    (x = 1 ∧ y = 1 ∧ z = 1) ∨ (x = -2 ∧ y = -2 ∧ z = -2) := by

  have eq1 : (y - x) * (1 - z) = 0 := by 
    nlinarith
  
  cases' (mul_eq_zero.mp eq1) with h3 h4
  · -- Case y - x = 0, so y = x
    have h4' : y = x := by linarith
    have eq2 : (z - y) * (1 - x) = 0 := by 
      nlinarith

    cases' (mul_eq_zero.mp eq2) with h6 h7
    · -- Case z - x = 0, so z = x
      have h8 : z = x := by linarith
      have h9 : x + x * x = 2 := by
        rw [show y = x by linarith [h4']] at h₀
        rw [show z = x by linarith [h8]] at h₀
        linarith
      have h10 : x ^ 2 + x - 2 = 0 := by
        nlinarith
      have h11 : (x - 1) * (x + 2) = 0 := by nlinarith
      cases' (mul_eq_zero.mp h11) with h12 h13
      · -- Case x = 1
        left
        constructor
        · linarith
        constructor
        · linarith [h4']
        · linarith [h8]
      · -- Case x = -2
        right
        constructor
        · linarith
        constructor
        · linarith [h4']
        · linarith [h8]
    · -- Case 1 - x = 0, so x = 1
      have h14 : x = 1 := by linarith
      have h15 : y = 1 := by linarith [h4', h14]
      have h17 : z = 1 := by
        rw [show x = 1 by linarith] at h₀
        rw [show y = 1 by linarith] at h₀
        nlinarith
      left
      constructor
      · linarith
      constructor
      · linarith
      · linarith
  · -- Case 1 - z = 0, so z = 1
    have h18 : z = 1 := by linarith
    have eq2 : (z - y) * (1 - x) = 0 := by 
      nlinarith
    rw [h18] at eq2
    cases' (mul_eq_zero.mp eq2) with h19 h20
    · -- Case 1 - y = 0, so y = 1
      have h21 : y = 1 := by linarith
      have h22 : x = 1 := by
        rw [h18] at h₀
        rw [h21] at h₀
        nlinarith
      left
      constructor
      · linarith
      constructor
      · linarith
      · linarith
    · -- Case 1 - x = 0, so x = 1
      have h23 : x = 1 := by linarith
      have h24 : y = 1 := by
        rw [h18] at h₀
        rw [h23] at h₀
        linarith
      left
      constructor
      · linarith
      constructor
      · linarith
      · linarith