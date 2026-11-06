import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_20824 {f : ℝ → ℝ} (hf : f = λ x => √(√(x ^ 2 - 16) - 3)) :
    /- 定义域可以表示为满足两个条件的实数集合：
       1. x^2-16 ≥ 0 （保证第一个根号下是非负数）
       2. √(x^2-16)-3 ≥ 0 （保证第二个根号下是非负数）
       这个集合等于 (-∞,-5]∪[5,+∞) -/
    {x : ℝ | x ^ 2 - 16 ≥ 0 ∧ √(x ^ 2 - 16) - 3 ≥ 0} = (Set.Iic (-5 : ℝ)) ∪ Set.Ici 5:= by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
  constructor
  · -- Assume x in left, need prove x in right
    rintro ⟨hc1, hc2⟩
    have h11 : √(x ^ 2 - 16) ≥ 3 := by linarith
    have h12 : x ^ 2 - 16 ≥ 9 := by
      have h21 : √(x ^ 2 - 16) ^ 2 = x ^ 2 - 16 := by 
        rw [Real.sq_sqrt]
        linarith
      nlinarith [Real.sqrt_nonneg (x ^ 2 - 16), Real.sq_sqrt (show x ^ 2 - 16 ≥ 0 by linarith), h11, h21]
    have : x ^ 2 ≥ 25 := by linarith
    by_cases h : x ≥ 0
    · -- If x ≥ 0, from x ^ 2 ≥ 25, get x ≥ 5
      right
      nlinarith [Real.sqrt_nonneg (x ^ 2 - 16)]
    · -- If not x ≥ 0, then x < 0. From x^2 >= 25, get x <= -5.
      left
      nlinarith [Real.sqrt_nonneg (x ^ 2 - 16)]
  · -- Assume x in right, prove in left
    rintro (hc1 | hc2)
    · -- Assume x ≤ -5
      have hc3 : x ^ 2 ≥ 25 := by nlinarith
      have hc4 : x ^ 2 - 16 ≥ 0 := by nlinarith
      have hc5 : √(x ^ 2 - 16) - 3 ≥ 0 := by
        have h111 : √(x ^ 2 - 16) ≥ 0 := Real.sqrt_nonneg (x ^ 2 - 16)
        by_contra h
        push_neg at h
        have h2 : √(x ^ 2 - 16) < (3 : ℝ) := by nlinarith
        have h3 : √(x ^ 2 - 16) ^ 2 < (3 : ℝ) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (x ^ 2 - 16), h2]
        have h4 : √(x ^ 2 - 16) ^ 2 = x ^ 2 - 16 := by
          rw [Real.sq_sqrt]
          linarith
        nlinarith [Real.sqrt_nonneg (x ^ 2 - 16), Real.sq_sqrt (show x ^ 2 - 16 ≥ 0 by linarith)]
      exact ⟨hc4, hc5⟩
    · -- Assume x ≥ 5
      have hc3 : x ^ 2 ≥ 25 := by nlinarith
      have hc4 : x ^ 2 - 16 ≥ 0 := by nlinarith
      have hc5 : √(x ^ 2 - 16) - 3 ≥ 0 := by
        have h111 : √(x ^ 2 - 16) ≥ 0 := Real.sqrt_nonneg (x ^ 2 - 16)
        by_contra h
        push_neg at h
        have h2 : √(x ^ 2 - 16) < (3 : ℝ) := by nlinarith
        have h3 : √(x ^ 2 - 16) ^ 2 < (3 : ℝ) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (x ^ 2 - 16), h2]
        have h4 : √(x ^ 2 - 16) ^ 2 = x ^ 2 - 16 := by
          rw [Real.sq_sqrt]
          linarith
        nlinarith [Real.sqrt_nonneg (x ^ 2 - 16), Real.sq_sqrt (show x ^ 2 - 16 ≥ 0 by linarith)]
      exact ⟨hc4, hc5⟩