import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12410 {p : ℝ} (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = cos (2 * x) + p * abs (cos x) + p) :
  IsGreatest (range f) (if p < -2 then p - 1 else if p ≥ -2 then 2 * p + 1 else p - 1) := by
  constructor
  · -- Show that this value is in the range of f
    by_cases h : p < -2
    · -- If p < -2, then h(p) = p - 1, which is f(π/2)
      rw [if_pos h]
      use Real.pi / 2
      have h2 : cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
      simp [h₀, h2, abs_of_nonneg, abs_of_nonpos, cos_two_mul, mul_add]
      <;> nlinarith
    · -- p ≥ -2
      by_cases h2 : p ≥ -2
      · -- If p ≥ -2, then h(p) = 2p + 1, which is f(0)
        rw [if_neg h]
        rw [if_pos h2]
        use 0
        simp [h₀, abs_of_nonneg, cos_zero, cos_two_mul]
        <;> nlinarith
      · -- p < -2, which contradicts h : ¬(p < -2)
        rw [if_neg h]
        rw [if_neg (show ¬(p ≥ -2) by linarith)]
        exfalso
        linarith
  · -- Show that this value is the greatest
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h₀ x] at hx
    by_cases h : p < -2
    · -- If p < -2, then h(p) = p - 1
      rw [if_pos h]
      have h2 : cos x ≥ -1 := by linarith [Real.neg_one_le_cos x, Real.cos_le_one x]
      have h3 : cos x ≤ 1 := Real.cos_le_one x
      by_cases h4 : cos x ≥ 0
      · -- If cos x ≥ 0, then |cos x| = cos x
        have h5 : abs (cos x) = cos x := abs_of_nonneg h4
        rw [h5] at hx
        have hcos2 : cos (2 * x) = 2 * (cos x) ^ 2 - 1 := by
          rw [cos_two_mul]
        rw [hcos2] at hx
        nlinarith [sq_nonneg (cos x - 1), sq_nonneg (cos x), sq_nonneg (cos x - 0), Real.sin_sq_add_cos_sq x]
      · -- If cos x < 0, then |cos x| = -cos x
        have h4' : cos x < 0 := by linarith
        have h5 : abs (cos x) = - (cos x) := abs_of_neg h4'
        rw [h5] at hx
        have hcos2 : cos (2 * x) = 2 * (cos x) ^ 2 - 1 := by
          rw [cos_two_mul]
        rw [hcos2] at hx
        nlinarith [sq_nonneg (cos x + 1), sq_nonneg (cos x), sq_nonneg (cos x - 0), Real.sin_sq_add_cos_sq x]
    · -- p ≥ -2
      by_cases h2 : p ≥ -2
      · -- If p ≥ -2, then h(p) = 2p + 1
        rw [if_neg h]
        rw [if_pos h2]
        have h2 : cos x ≥ -1 := by linarith [Real.neg_one_le_cos x, Real.cos_le_one x]
        have h3 : cos x ≤ 1 := Real.cos_le_one x
        by_cases h4 : cos x ≥ 0
        · -- If cos x ≥ 0, then |cos x| = cos x
          have h5 : abs (cos x) = cos x := abs_of_nonneg h4
          rw [h5] at hx
          have hcos2 : cos (2 * x) = 2 * (cos x) ^ 2 - 1 := by
            rw [cos_two_mul]
          rw [hcos2] at hx
          nlinarith [sq_nonneg (cos x - 1), sq_nonneg (cos x + 1), sq_nonneg (cos x), Real.sin_sq_add_cos_sq x]
        · -- If cos x < 0, then |cos x| = -cos x
          have h4' : cos x < 0 := by linarith
          have h5 : abs (cos x) = - (cos x) := abs_of_neg h4'
          rw [h5] at hx
          have hcos2 : cos (2 * x) = 2 * (cos x) ^ 2 - 1 := by
            rw [cos_two_mul]
          rw [hcos2] at hx
          nlinarith [sq_nonneg (cos x + 1), sq_nonneg (cos x - 1), sq_nonneg (cos x), Real.sin_sq_add_cos_sq x]
      · -- p < -2, which contradicts h : ¬(p < -2)
        rw [if_neg h]
        rw [if_neg (show ¬(p ≥ -2) by linarith)]
        exfalso
        linarith