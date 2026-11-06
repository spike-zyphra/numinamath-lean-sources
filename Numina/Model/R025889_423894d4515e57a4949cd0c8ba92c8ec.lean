import Mathlib


open BigOperators Real Set


theorem algebra_327699 :
  IsLeast {u : ℝ | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ a + b = 2 ∧ u = sqrt (a^2 + 1) + sqrt (b^2 + 4)} (sqrt 13) := by
  constructor
  · -- Show sqrt 13 attained
    use 2 / 3, (4 / 3)
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    have h1 : sqrt ((2 / 3: ℝ) ^ 2 + 1) = sqrt 13 / 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num [Real.sqrt_sq, mul_add, mul_assoc]
      <;> nlinarith [Real.sqrt_nonneg 13]
    have h2 : sqrt ((4 / 3: ℝ) ^ 2 + 4) = 2 * sqrt 13 / 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num [Real.sqrt_sq, mul_add, mul_assoc]
      <;> nlinarith [Real.sqrt_nonneg 13]
    rw [h1, h2]
    field_simp
    <;> ring_nf <;> norm_num
  · -- Show sqrt 13 is minimal
    intro t ht
    rcases ht with ⟨a, b, ha, hb, hab, ht⟩
    -- We need to prove $t \ge \sqrt{13}$. And since $t = \sqrt{a^2 + 1} + \sqrt{b^2 + 4}$, we need to prove that this sum is minimal.
    have h1 : sqrt (a ^2 + 1) + sqrt (b ^2 + 4) ≥ sqrt 13 := by
      have h2 : b = 2 - a := by linarith
      rw [h2]
      have h11 : (sqrt (a ^2 + 1) + sqrt ((2 - a) ^2 + 4)) ^ 2 ≥ (sqrt 13) ^ 2 := by
        have h12 : (sqrt (a ^2 + 1) + sqrt ((2 - a) ^2 + 4)) ^2 = (sqrt (a ^2 + 1)) ^ 2 + (sqrt ((2 - a) ^2 + 4)) ^ 2 + 2 * (sqrt (a ^2 + 1) * sqrt ((2 - a) ^2 + 4)) := by ring
        rw [h12]
        have h13 : (sqrt 13) ^ 2 = 13 := Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)
        have h14 : (sqrt (a ^2 + 1)) ^ 2 = a ^2 + 1 := Real.sq_sqrt (by positivity)
        have h15 : (sqrt ((2 - a) ^2 + 4)) ^ 2 = (2 - a) ^2 + 4 := Real.sq_sqrt (by positivity)
        have h16 : sqrt (a ^2 + 1) * sqrt ((2 - a) ^2 + 4) ≥ 0 := by positivity
        nlinarith [sq_nonneg (a - 2 / 3), sq_nonneg ((2 - a) - 4 / 3), sq_nonneg (a ^2 - 4 / 9), sq_nonneg ((2 - a) ^2 - 16 / 9), Real.sqrt_nonneg 13, mul_nonneg (Real.sqrt_nonneg (a^2 +1)) (Real.sqrt_nonneg ((2-a)^2 +4))]
      nlinarith [Real.sqrt_nonneg (a ^2 + 1), Real.sqrt_nonneg ((2 - a) ^2 + 4), Real.sqrt_nonneg 13]
    have ht2 : t = sqrt (a ^2 + 1) + sqrt (b ^2 + 4) := by
      nlinarith
    linarith [ht2, h1]