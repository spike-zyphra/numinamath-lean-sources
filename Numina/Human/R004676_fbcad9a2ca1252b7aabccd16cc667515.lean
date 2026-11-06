import Mathlib

/- 1. Given distinct complex numbers $a$ and $b$ satisfying $a b \neq 0$, the set $\{a, b\}=\left\{a^{2}, b^{2}\right\}$. Then $a+b=$ $\qquad$ . -/
theorem algebra_298015 (a b : ℂ) (h₁ : a ≠ b) (h₂ : a * b ≠ 0) (h : ({a, b} : Set _) = {a ^ 2, b ^ 2}) : a + b = -1 := by
  -- We get `a ≠ 0` and `b ≠ 0` from `h₂`
  replace ⟨h₂, h₃⟩ := mul_ne_zero_iff.mp h₂
  -- We have `a = a ^ 2` and `b = b ^ 2` or `a = b ^ 2` and `b = a ^ 2`
  rw [Set.pair_eq_pair_iff] at h
  -- Case analysis on the two possible equalities
  rcases h with ⟨h₄, h₅⟩ | ⟨h₄, h₅⟩
  . -- If `a = a ^ 2` and `b = b ^ 2`, then `a = 0` or `a = 1`, and `b = 0` or `b = 1`
    -- But it contradicts to `a ≠ 0`, `b ≠ 0` and `a ≠ b`
    replace h₄ : a * (a - 1) = 0 := by linear_combination -h₄
    replace h₅ : b * (b - 1) = 0 := by linear_combination -h₅
    simp [sub_eq_zero, h₂, h₃] at h₄ h₅
    simp [h₄, ← h₅] at h₁
  . -- If `a = b ^ 2` and `b = a ^ 2`
    -- We subtract the two equations and get `(a - b) * (a + b + 1) = 0`
    -- So `a + b = -1`.
    have h₆ : (a - b) * (a + b - (-1)) = 0 := by linear_combination h₄ - h₅
    simp [-sub_neg_eq_add, sub_eq_zero] at h₆
    simpa [h₁] using h₆
