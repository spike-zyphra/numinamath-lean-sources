import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_253817 (f : ℝ → ℝ) (hf : f = λ x => x^3 - x) :
    IsGreatest {x | ∃ a b, a < b ∧ f a = f b ∧ x = b - a} 2 := by
  constructor
  · -- Let's prove that 2 belongs to the set
    use -1, 1
    constructor
    · norm_num
    constructor
    · -- f(-1) = f(1)
      rw [hf]
      norm_num
    · -- 2 = 1 - (-1)
      norm_num
  · -- Let's prove that any value in the set ≤ 2
    intro x hx
    rcases hx with ⟨a, b, h1, h2, h3⟩
    rw [h3]
    rw [hf] at h2
    simp at h2
    by_contra h
    push_neg at h
    have h34 : a ^ 3 - a = b ^ 3 - b := by nlinarith
    have h35 : (b - a) * (a^2 + a * b + b^2 - 1) = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a^2 - b^2), sq_nonneg (a^2 + b^2)]
    cases' (mul_eq_zero.mp h35) with h40 h41
    · -- Case b - a = 0, which contradicts a < b
      nlinarith -- f g l
    · -- Case a^2 + a * b + b^2 - 1 = 0
      nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (a + b)]