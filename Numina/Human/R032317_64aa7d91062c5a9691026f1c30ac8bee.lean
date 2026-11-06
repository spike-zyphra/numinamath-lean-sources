import Mathlib

theorem algebra_182688 (f g : ℝ → ℝ) :
    (∀ x y, 1 + x ^ 2016 * y ^ 2016 = f x * g y) ↔
    False := by
  constructor 
  -- necessity
  . intro H
    -- This gives us 1 + 0^2016 * 0^2016 = f(0) * g(0), which simplifies to 1 = f(0) * g(0)
    have h₁ := H 0 0
    -- This gives us 1 + 1^2016 * 0^2016 = f(1) * g(0), which simplifies to 1 = f(1) * g(0)
    have h₂ := H 1 0
    -- This gives us 1 + 0^2016 * 1^2016 = f(0) * g(1), which simplifies to 1 = f(0) * g(1)
    have h₃ := H 0 1
    -- This gives us 1 + 1^2016 * 1^2016 = f(1) * g(1), which simplifies to 2 = f(1) * g(1)
    have h₄ := H 1 1
    
    norm_num at h₁ h₂ h₃ h₄
    
    -- nlinarith may close the goal here

    -- from h₁ and h₂, we get f 0 = f 1
    have h₅ : f 0 = f 1 := by
      rw [h₂] at h₁
      apply mul_eq_mul_right_iff.mp at h₁
      have : g 0 ≠ 0 := by
        by_contra!
        norm_num [this] at h₂
      tauto
    
    -- but with h₃, h₄ and h₅, we get 1 = 2, a contradiction.
    norm_num [h₅, ← h₄] at h₃

  -- sufficiency
  . exact False.elim