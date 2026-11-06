import Mathlib

open Real Set
open scoped Real

/- 10. Let $\alpha, \beta \in\left(0, \frac{\pi}{2}\right)$. Prove: $\cos \alpha+\cos \beta+\sqrt{2} \sin \alpha \sin \beta \leq \frac{3 \sqrt{2}}{2}$. -/
theorem inequalities_226051 (α β : ℝ) (hα : α ∈ Ioo 0 (π/2)) (hβ : β ∈ Ioo 0 (π/2)) :
    cos α + cos β + sqrt 2 * sin α * sin β ≤ 3 * sqrt 2 / 2 := by
  simp at hα hβ
  calc
    -- Use cos sum formula
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) + √2 / 2 * (2 * sin α * sin β) := by simp [cos_add_cos]; linarith
    -- Use sin multiplication formula
    _ = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) + √2 / 2 * (cos (α - β) - cos (α + β)) := by simp [two_mul_sin_mul_sin]
    -- Bound cos ((α - β) / 2) by 1
    _ ≤ 2 * cos ((α + β) / 2) * 1 + √2 / 2 * (cos (α - β) - cos (α + β)) := by
      apply add_le_add_right
      rw [mul_le_mul_left]
      · -- cos ((α - β) / 2) ≤ 1
        exact cos_le_one _
      -- Show that 2 * cos ((α - β) / 2) is positive
      apply mul_pos (by positivity)
      apply cos_pos_of_mem_Ioo
      simp
      exact ⟨by linarith, by linarith⟩
    -- Bound cos (α - β) above by 1
    _ ≤ 2 * cos ((α + β) / 2) + √2 / 2 * (1 - cos (α + β)) := by
      rw [mul_one]
      apply add_le_add_left
      rw [mul_le_mul_left (by positivity)]
      apply sub_le_sub_right
      exact cos_le_one _
    -- Rewrite with half angle identity
    _ = 2 * cos ((α + β) / 2) + √2 / 2 * (2 - 2 * cos ((α + β) / 2) ^ 2) := by
      conv =>
        rhs; rhs; rhs
        -- Use cosine half angle identity
        rw [cos_half (by linarith) (by linarith), sq_sqrt (by linarith [neg_one_le_cos (α + β)])]
        -- Simplify
        rw [mul_div_cancel₀ _ (by positivity), ← sub_sub]
        norm_num
    _ = √2 - √2 * cos ((α + β) / 2) ^ 2 + 2 * cos ((α + β) / 2) := by linarith
    -- Complete the square
    _ = 3 * √2 / 2 - √2 * (cos ((α + β) / 2) - √2 / 2) ^ 2 := by
      rw [sub_sq, ← mul_div_assoc, mul_assoc, mul_div_assoc 2 _ 2, mul_div_cancel₀ _ (by positivity), div_pow, sq_sqrt (by positivity), mul_add, mul_sub, ← sub_sub, ← sub_add]
      norm_num
      rw [mul_one_div]
      rw [show 3 * √2 / 2 = √2 + √2 / 2 by linarith, mul_comm (cos _) (√2), ← mul_assoc, ← pow_two, sq_sqrt (by positivity)]
      linarith
    _ ≤ 3 * √2 / 2 := by
      have : 0 ≤ √2 * (cos ((α + β) / 2) - √2 / 2) ^ 2 := by positivity
      linarith