import Mathlib

open Set

theorem algebra_525610 :
    {m : ℝ | ∃ x y, x ≠ y ∧ x ∈ Ioc 0 3 ∧ y ∈ Ioc 0 3 ∧
    x^2 - (m + 1)*x + 4 = 0 ∧ y^2 - (m + 1)*y + 4 = 0} = Set.Ioc 3 (10/3) := by 
  ext m 
  simp only [Set.mem_setOf_eq, Set.mem_Ioc]
  constructor 
  · -- Assume there exist two distinct roots x, y in (0,3]
    rintro ⟨x, y, hxy, hx, hy, heq1, heq2⟩
    rcases hx with ⟨hx0, hx3⟩
    rcases hy with ⟨hy0, hy3⟩
    have h1 : m + 1 = x + y := by 
      have h_sub : (x ^ 2 - (m + 1) * x + 4) - (y ^ 2 - (m + 1) * y + 4) = 0 := by 
        linarith [heq1, heq2]
      have h2 : (x - y) * (x + y - (m + 1)) = 0 := by 
        ring_nf at h_sub ⊢ 
        linarith 
      cases' (mul_eq_zero.mp h2) with h3 h4 
      · -- Assume x - y = 0 
        exfalso 
        apply hxy 
        linarith
      · -- Assume x + y - (m + 1) = 0 
        linarith 
    have h2 : x * y = 4 := by 
      rw [show m + 1 = x + y by linarith [h1]] at heq1
      nlinarith 
    constructor 
    · -- Prove m > 3 
      nlinarith [sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by 
        intro h'
        apply hxy 
        linarith 
      ), sq_nonneg (x - y), sq_nonneg (x + y - 4)]
    · -- Prove m ≤ 10/3 
      nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (x * y - 4), mul_self_nonneg (x - y), mul_self_nonneg (x - 4 / 3), mul_self_nonneg (y - 4 / 3)]
  · -- Assume m ∈ (3, 10/3]
    rintro ⟨hm1, hm2⟩ 
    have h1 : (m + 1) ^ 2 - 16 > 0 := by 
      nlinarith 
    use (m + 1 + Real.sqrt ((m + 1) ^ 2 - 16)) / 2, (m + 1 - Real.sqrt ((m + 1) ^ 2 - 16)) / 2 
    constructor 
    · -- Show x ≠ y 
      by_contra h 
      nlinarith [Real.sqrt_nonneg ((m + 1) ^ 2 - 16), Real.sq_sqrt (show (m + 1) ^ 2 - 16 ≥ 0 by nlinarith)]
    constructor 
    · -- Show x ∈ (0, 3] 
      constructor 
      · -- Show 0 < x 
        nlinarith [Real.sqrt_nonneg ((m + 1) ^ 2 - 16), Real.sq_sqrt (show (m + 1) ^ 2 - 16 ≥ 0 by nlinarith)]
      · -- Show x ≤ 3 
        nlinarith [Real.sqrt_nonneg ((m + 1) ^ 2 - 16), Real.sq_sqrt (show (m + 1) ^ 2 - 16 ≥ 0 by nlinarith)]
    constructor 
    · -- Show y ∈ (0, 3] 
      constructor 
      · -- Show 0 < y 
        nlinarith [Real.sqrt_nonneg ((m + 1) ^ 2 - 16), Real.sq_sqrt (show (m + 1) ^ 2 - 16 ≥ 0 by nlinarith)]
      · -- Show y ≤ 3 
        nlinarith [Real.sqrt_nonneg ((m + 1) ^ 2 - 16), Real.sq_sqrt (show (m + 1) ^ 2 - 16 ≥ 0 by nlinarith)]
    constructor 
    · -- Show x^2 - (m + 1)*x + 4 = 0 
      nlinarith [Real.sqrt_nonneg ((m + 1) ^ 2 - 16), Real.sq_sqrt (show (m + 1) ^ 2 - 16 ≥ 0 by nlinarith)]
    · -- Show y^2 - (m + 1)*y + 4 = 0 
      nlinarith [Real.sqrt_nonneg ((m + 1) ^ 2 - 16), Real.sq_sqrt (show (m + 1) ^ 2 - 16 ≥ 0 by nlinarith)]