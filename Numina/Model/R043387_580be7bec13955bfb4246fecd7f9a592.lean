import Mathlib

theorem algebra_197909 (pair : Fin 4 → ℝ) (p q r s t : (Fin 4 → ℝ) → Prop) 
    (hp : ∀ x, p x ↔ ∀ n, x n ≠ 0)
    (hq : ∀ x, q x ↔ x 0 * x 3 = x 1 * x 2)
    (hr : ∀ x, r x ↔ x 0 + x 3 = x 1 + x 2 + 7)
    (hs : ∀ x, s x ↔ x 0 ^ 2 + x 3 ^ 2 = x 1 ^ 2 + x 2 ^ 2 + 21)
    (ht : ∀ x, t x ↔ x 0 ^ 4 + x 3 ^ 4 = x 1 ^ 4 + x 2 ^ 4 + 2625) :
    {x | p x ∧ q x ∧ r x ∧ s x ∧ t x} = {![-3, -6, 4, 8], ![-3, 4, -6, 8], ![8, -6, 4, -3], ![8, 4, -6, -3]} := by 
  ext x
  simp [hp, hq, hr, hs, ht]
  constructor
  · -- Forward direction: if x satisfies all conditions, prove membership in the finite set
    rintro ⟨hp, hq, hr, hs, ht⟩
    have h1 : x 0 + x 3 = (x 1 + x 2) + 7 := by linarith 
    have h2 : x 0 ^ 2 + x 3 ^ 2 = x 1 ^ 2 + x 2 ^ 2 + 21 := by linarith
    have h3 : x 0 ^ 4 + x 3 ^ 4 = x 1 ^ 4 + x 2 ^ 4 + 2625 := by linarith 
    have h4 : x 0 * x 3 = x 1 * x 2 := by linarith 
    have h5 : (x 0 + x 3) ^ 2 = (x 1 + x 2) ^ 2 + 21 := by
      nlinarith [hs, h4]
    have h6 : x 1 + x 2 = -2 := by 
      nlinarith [h1, h5]
    have h7 : x 0 + x 3 = 5 := by 
      linarith [h1, h6]
    have h8 : x 0 * x 3 = -24 := by 
      nlinarith [ht, h4, h7, h6, sq_nonneg (x 0 - x 3), sq_nonneg (x 1 - x 2)]
    have h9 : x 1 * x 2 = -24 := by 
      nlinarith [h4, h8]
    have h10 : (x 0 - 8) * (x 0 + 3) = 0 := by 
      nlinarith [sq_nonneg (x 0 - 8), sq_nonneg (x 0 + 3), h7, h8]
    cases' (mul_eq_zero.1 h10) with h11 h12
    · -- Case where x 0 = 8
      have hx0 : x 0 = 8 := by linarith 
      have hx3 : x 3 = -3 := by linarith 
      have h13 : (x 1 - 4) * (x 1 + 6) = 0 := by 
        nlinarith [sq_nonneg (x 1 - 4), sq_nonneg (x 1 + 6), h6, h9]
      cases' (mul_eq_zero.1 h13) with h14 h15
      · -- Case where x 1 = 4
        have hx1 : x 1 = 4 := by linarith 
        have hx2 : x 2 = -6 := by linarith 
        -- Fourth solution: [8, 4, -6, -3]
        have h11' : x = ![8, 4, -6, -3] := by 
          funext i
          fin_cases i <;> simp [hx0, hx1, hx2, hx3]
        simp only [h11', Fin.isValue] at *
        <;> tauto 
      · -- Case where x 1 = -6
        have hx1 : x 1 = -6 := by linarith 
        have hx2 : x 2 = 4 := by linarith 
        -- Third solution: [8, -6, 4, -3]
        have h11' : x = ![8, -6, 4, -3] := by 
          funext i
          fin_cases i <;> simp [hx0, hx1, hx2, hx3]
        simp only [h11', Fin.isValue] at *
        <;> tauto 
    · -- Case where x 0 = -3
      have hx0 : x 0 = -3 := by linarith 
      have hx3 : x 3 = 8 := by linarith 
      have h13 : (x 1 - 4) * (x 1 + 6) = 0 := by 
        nlinarith [sq_nonneg (x 1 - 4), sq_nonneg (x 1 + 6), h6, h9]
      cases' (mul_eq_zero.1 h13) with h14 h15
      · -- Case where x 1 = 4
        have hx1 : x 1 = 4 := by linarith 
        have hx2 : x 2 = -6 := by linarith 
        -- Second solution: [-3, 4, -6, 8]
        have h11' : x = ![-3, 4, -6, 8] := by 
          funext i
          fin_cases i <;> simp [hx0, hx1, hx2, hx3]
        simp only [h11', Fin.isValue] at *
        <;> tauto 
      · -- Case where x 1 = -6
        have hx1 : x 1 = -6 := by linarith 
        have hx2 : x 2 = 4 := by linarith 
        -- First solution: [-3, -6, 4, 8]
        have h11' : x = ![-3, -6, 4, 8] := by 
          funext i
          fin_cases i <;> simp [hx0, hx1, hx2, hx3]
        simp only [h11', Fin.isValue] at *
        <;> tauto 
  · -- Backward direction: if x is in the finite set, prove it satisfies all conditions
    rintro (rfl | rfl | rfl | rfl)
    · -- First vector: ![-3, -6, 4, 8]
      constructor
      · -- p: all non-zero
        intro n
        fin_cases n <;> norm_num 
      constructor
      · -- q: product
        norm_num 
      constructor
      · -- r: sum
        norm_num 
      constructor
      · -- s: squares
        norm_num 
      · -- t: fourth powers
        norm_num 
    · -- Second vector: ![-3, 4, -6, 8]
      constructor
      · -- p: all non-zero
        intro n
        fin_cases n <;> norm_num 
      constructor
      · -- q: product
        norm_num 
      constructor
      · -- r: sum
        norm_num 
      constructor
      · -- s: squares
        norm_num 
      · -- t: fourth powers
        norm_num 
    · -- Third vector: ![8, -6, 4, -3]
      constructor
      · -- p: all non-zero
        intro n
        fin_cases n <;> norm_num 
      constructor
      · -- q: product
        norm_num 
      constructor
      · -- r: sum
        norm_num 
      constructor
      · -- s: squares
        norm_num 
      · -- t: fourth powers
        norm_num 
    · -- Fourth vector: ![8, 4, -6, -3]
      constructor
      · -- p: all non-zero
        intro n
        fin_cases n <;> norm_num 
      constructor
      · -- q: product
        norm_num 
      constructor
      · -- r: sum
        norm_num 
      constructor
      · -- s: squares
        norm_num 
      · -- t: fourth powers
        norm_num