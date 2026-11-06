import Mathlib

theorem algebra_316505 (a b c : ℤ) (ha : 0 < a) (hA : a * (-1)^2 + b * (-1) + c = 4)
    (hB : a * 2^2 + b * 2 + c = 1) (hroots : ∃ x1 x2, x1 ≠ x2 ∧ a * x1^2 + b * x1 + c = 0 ∧
    a * x2^2 + b * x2 + c = 0) :
    b + c ≤ -4 := by
  rcases hroots with ⟨x1, x2, hx12, hx1, hx2⟩
  have eq1 : a - b + c = 4 := by 
    nlinarith 
  have eq2 : 4 * a + 2 * b + c = 1 := by
    nlinarith 
  have eq3 : a + b = -1 := by
    linarith [eq1, eq2]
  have eq4 : c = 3 - 2 * a := by 
    nlinarith [eq1, eq3]
  have eq5 : b = -1 - a := by 
    linarith [eq3]
  have h4 : (x1 - x2) * (a * (x1 + x2) + b) = 0 := by
    have eq7 : a * (x1^2 - x2^2) + b * (x1 - x2) = 0 := by 
      nlinarith 
    have eq8 : (x1 - x2) * (a * (x1 + x2) + b) = 0 := by
      linarith [eq7] 
    linarith [eq8] 
  have h5 : a * (x1 + x2) + b = 0 := by
    cases (mul_eq_zero.1 h4) with
    | inl h6 => 
      have h7 : x1 = x2 := by 
        omega 
      exfalso 
      apply hx12 
      omega 
    | inr h7 => 
      linarith 
  have hdisc : b ^ 2 - 4 * a * c > 0 := by
    by_contra h
    push_neg at h 
    have h8 : (x1 - x2) ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), 
                  h, sq_nonneg (a * x1), sq_nonneg (a * x2), sq_nonneg (b * x1), sq_nonneg (b * x2), 
                  sq_nonneg (c), sq_nonneg (b ^ 2 - 4 * a * c)
                ]
    have h9 : (x1 - x2) ^ 2 > 0 := by 
      apply pow_two_pos_of_ne_zero 
      intro h 
      apply hx12 
      linarith 
    linarith 
  rw [show b = -1 - a by linarith [eq3]] at hdisc
  rw [show c = 3 - 2 * a by linarith [eq1, eq3]] at hdisc
  have h1 : 9 * a ^ 2 - 10 * a + 1 > 0 := by 
    nlinarith 
  have h7 : a ≥ 2 := by 
    nlinarith 
  have eq5 : b + c = 2 - 3 * a := by 
    linarith [eq3, eq4] 
  nlinarith