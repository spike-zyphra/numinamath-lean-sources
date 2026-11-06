import Mathlib

theorem algebra_173811 (x y z : ℝ) (h₀ : x + y - z = -1) (h₁ : x ^ 2 - y ^ 2 + z ^ 2 = 1)
    (h₂ : -x ^ 3 + y ^ 3 + z ^ 3 = -1) :
    (x = 1 ∧ y = -1 ∧ z = 1) ∨ (x = -1 ∧ y = -1 ∧ z = -1) := by

  have h3 : z = x + y + 1 := by
    linarith [h₀]

  rw [show z = x + y + 1 by linarith] at h₁
  have h4 : (x + y) * (x + 1) = 0 := by
    nlinarith [h₁]

  cases' (mul_eq_zero.1 h4) with h5 h6
  · -- Assume x + y = 0, so y = -x.
    have h7 : y = -x := by 
      linarith 

    have h8 : z = 1 := by 
      nlinarith [h3, h7]

    have h9 : x = 1 := by
      rw [show y = -x by linarith [h7], show z = 1 by linarith [h8]] at h₂
      have h10 : x^3 = 1 := by 
        nlinarith [h₂]
      have h11 : x = 1 := by
        have h12 : x^3 - 1 = 0 := by 
          linarith 
        have h13 : (x - 1) * (x^2 + x + 1) = 0 := by 
          ring_nf at h12 ⊢ 
          nlinarith 
        cases' (mul_eq_zero.1 h13) with h14 h15
        · -- Assume x -1 =0 
          linarith
        · -- Assume x^2 + x +1 =0 
          nlinarith [sq_nonneg (x + 1/2)]
      linarith

    left
    constructor
    · linarith [h9]
    constructor
    · linarith [h7, h9]
    · linarith [h8, h9]

  · -- Assume x + 1 = 0, so x = -1.
    have h10 : x = -1 := by 
      linarith

    have h11 : z = y := by 
      nlinarith [h3, h10]

    have h12 : y = -1 := by
      rw [show x = -1 by linarith [h10], show z = y by linarith [h11]] at h₂
      have h13 : y^3 = -1 := by 
        nlinarith [h₂]
      have h14 : y = -1 := by 
        have h15 : y^3 + 1 = 0 := by 
          linarith 
        have h16 : (y + 1) * (y^2 - y + 1) = 0 := by 
          ring_nf at h15 ⊢ 
          nlinarith 
        cases' (mul_eq_zero.1 h16) with h17 h18
        · -- Assume y +1 =0 
          linarith
        · -- Assume y^2 -y +1 =0 
          nlinarith [sq_nonneg (y - 1/2)]
      linarith

    right
    constructor
    · linarith 
    constructor
    · linarith 
    · linarith [h11, h12]