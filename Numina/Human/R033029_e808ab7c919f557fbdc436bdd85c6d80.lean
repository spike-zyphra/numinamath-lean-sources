import Mathlib

/-
  Given that the positive numbers $a$ and $b$ satisfy the equation $ab = a + b + 3$, and $ab \geq m$ always holds true, find the range of values for the real number $m$.
-/
theorem algebra_9064 (m : ℝ) :
    (∀ a b : ℝ, (a > 0 ∧ b > 0 ∧ a * b = a + b + 3) → a * b ≥ m) ↔ m ≤ 9 := by
  constructor
  · intro h
    by_contra!
    -- consider the special case where a = b = 3, then a * b = 9, so m is at most 9.
    specialize h 3 3 (by norm_num)
    linarith
  · intro hm
    rintro a b ⟨age, bge, abeq⟩
    -- change the goal to: √ (a * b) ≥ 3.
    suffices goal : a * b ≥ 9 from by linarith
    have hab : a * b = √ (a * b) * √ (a * b) := by refine Eq.symm (Real.mul_self_sqrt ?h); linarith
    suffices goal : √ (a * b) ≥ 3 from by nlinarith
    -- here we prove the easiest version of AM-GM inequality, which I didn't find in mathlib
    have : a + b ≥ 2 * √ (a * b) := by
      have : 2 * √ (a * b) = √ (4 * (a * b)) := by
        field_simp
        refine Eq.symm ((fun {x y} ↦ Real.sqrt_eq_cases.mpr) ?_)
        norm_num
      rw [this]
      refine (Real.sqrt_le_left ?hy).mpr ?_
      linarith
      have : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
      rw [this]
      suffices goal : a ^ 2 - 2 * a * b + b ^ 2 ≥ 0 from by linarith
      have : a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
      rw [this]
      nlinarith
    -- from a * b = a + b + 3 and a + b ≥ 2 √ (a * b), we derive the following inequality
    have hc : a * b - 2 * √ (a * b) - 3 ≥ 0 := by linarith
    -- substitute √ (a * b) * √ (a * b) for a * b
    nth_rw 1 [hab] at hc
    -- factorization
    have : √ (a * b) * √ (a * b) - 2 * √ (a * b) - 3 = (√ (a * b) - 3) * (√ (a * b) + 1) := by ring
    rw [this] at hc
    -- now we have (√(a * b) - 3) * (√(a * b) + 1) ≥ 0.
    -- it is easy to show (√(a * b) + 1) > 0:
    have : √ (a * b) > 0 := by simp; linarith
    have : √ (a * b) + 1 > 0 := by linarith
    -- thus we must have (√(a * b) - 3) ≥ 0, which is what we need
    have := (mul_nonneg_iff_pos_imp_nonneg.mp hc).2 this
    linarith