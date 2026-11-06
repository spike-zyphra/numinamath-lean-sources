import Mathlib

theorem algebra_214677 :
    {(x, y) : ℝ × ℝ | x^2 + y^3 = x + 1 ∧ x^3 + y^2 = y + 1} =
    {(1, 1), (-1, -1)} := by 
  ext ⟨x, y⟩
  simp 
  constructor 
  · -- Forward: if (x,y) is in the system, it's in the result set
    rintro ⟨h₁, h₂⟩
    have eq1 : x ^ 2 - x ^ 3 + y ^ 3 - y ^ 2 = x - y := by 
      nlinarith 
    have h4 : (x - y) * (x^2 - x * y + y^2 - x - y + 1) = 0 := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x^2 - y^2), sq_nonneg (x^3 - y^3)]
    cases' (mul_eq_zero.mp h4) with h5 h6 
    · -- Case where x = y
      have hy : y = x := by linarith 
      rw [show y = x by linarith] at h₁ h₂
      have h7 : x ^ 3 + x ^ 2 - x - 1 = 0 := by 
        nlinarith 
      have h8 : (x - 1) * (x + 1) ^ 2 = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h8) with h9 h10
      · -- Case where x - 1 = 0, so x = 1
        have hx1 : x = 1 := by linarith 
        have hy1 : y = 1 := by linarith [hx1, hy]
        left 
        constructor 
        · linarith 
        · linarith 
      · -- Case where (x + 1) ^ 2 = 0
        have h11 : x + 1 = 0 := by 
          apply pow_eq_zero 
          exact h10 
        have hx2 : x = -1 := by linarith 
        have hy2 : y = -1 := by linarith [hx2, hy]
        right 
        constructor 
        · linarith 
        · linarith 
    · -- Case where the quadratic is zero: x^2 -x *y + y^2 -x -y +1 =0
      have h7 : (x - 1) ^ 2 + (y - 1) ^ 2 + (x - y) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
      have hx_eq1 : (x - 1) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y)]
      have hy_eq1 : (y - 1) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y)]
      have hxy_eq : (x - y) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y)]
      have hx1 : x = 1 := by 
        nlinarith 
      have hy1 : y = 1 := by 
        nlinarith 
      left 
      constructor 
      · linarith 
      · linarith 
  · -- Backward: if (x,y) is in the result set, it's in the system
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Case (1, 1)
      constructor
      · -- First equation
        norm_num 
      · -- Second equation
        norm_num 
    · -- Case (-1, -1)
      constructor
      · -- First equation
        norm_num 
      · -- Second equation
        norm_num