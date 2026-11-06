import Mathlib

/- When $a < 0$, the solution to the equation $x|x| + |x| - x - a = 0$ is. -/
theorem algebra_9029 (a : ℝ) (ha : a < 0) (x : ℝ) :
  x * abs x + abs x - x - a = 0 ↔ x = -1 - Real.sqrt (1 - a) := by

  have ha₀ : 0 ≤ √(1 - a) := by simp

  constructor <;> intro h

  . -- Prove the forward implication (→):
    by_cases hx : x < 0
    . -- Case 1: x < 0
      have hx₀ : |x| = x ∧ 0 ≤ x ∨ |x| = -x ∧ x < 0 := abs_cases x
      have : |x| = -x := by
        cases hx₀ with
        | inl h₁ => linarith
        | inr h₁ => apply And.left h₁
      simp_all
      have : -(x * x) + -x - x - a = - (1 + x) ^ 2 + 1 - a := by ring
      rw [this] at h
      have : (1 + x) ^ 2 = 1 - a := by linarith
      have ha₁ : 0 ≤ 1 - a := by linarith
      let t : √(1 - a) ^ 2 = 1 - a := Real.sq_sqrt ha₁
      rw [← t] at this
      rw [sq_eq_sq_iff_eq_or_eq_neg] at this
      cases this
      . -- Case 1.1: x = -1 + √(1 - a)
        rename_i hx₀
        have h1le1a : 1 ≤ 1 - a := by linarith
        rw [← Real.one_le_sqrt, ← hx₀] at h1le1a
        linarith
      . -- Case 1.2: x = -1 - √(1 - a)
        nlinarith

    . -- Case 2: x >= 0
      simp_all
      rw [← abs_eq_self] at hx
      rw [hx] at h
      simp_all
      have : x ^ 2 = a := by linarith
      rw [← this] at ha
      nlinarith


  . -- Prove the backward implication (←):
    have hxle0 : x ≤ 0 := by linarith
    rw [← abs_eq_neg_self] at hxle0
    rw [hxle0]

    have : 0 ≤ 1 - a := by linarith

    have h₀ : x * -x + -x - x - a = 0 :=
      calc
        x * -x + -x - x - a = - (1 + x) ^ 2 + 1 - a := by ring
        _ = - (1 + -1 - √(1 - a)) ^ 2 + 1 - a := by rw [h, ← add_sub_assoc]
        _ = - (√(1 - a)) ^ 2 + 1 - a := by norm_num
        _ = - (1 - a) + 1 - a := by rw [Real.sq_sqrt this]
        _ = 0 := by norm_num
    exact h₀
