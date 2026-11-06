import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_305562 {f : ℝ → ℝ}
  (hf : ∀ x, x ≤ 0 → f x = x - ⌊x⌋)
  (hf' : ∀ x, x > 0 → f x = f (x - 1)) (k : ℝ) (hk : k > 0)
  (hroots : ∀ x, f x = k * x + k → x = 0 ∨ x = 1) :
  1 / 4 ≤ k ∧ k < 1 / 3 := by 
  specialize hroots (-1) (by 
    have hf'': f (-1) = 0 := by 
      specialize hf (-1) (by norm_num)
      norm_num at hf ⊢
      <;> linarith 
    -- Now compute k * (-1) + k 
    have eq1 : k * (-1) + k = (0 : ℝ) := by
      ring
    -- Then f (-1) = 0
    rw [hf'']
    <;> linarith 
  )
  -- Now obtain contradiction since -1 is not 0 or 1 
  cases hroots with 
  | inl h => 
      -- Absurd since -1 ≠ 0 
      exfalso 
      linarith 
  | inr h => 
      -- Absurd since -1 ≠ 1 
      exfalso 
      linarith