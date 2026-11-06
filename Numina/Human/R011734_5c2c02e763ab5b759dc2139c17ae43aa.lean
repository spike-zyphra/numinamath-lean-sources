import Mathlib

/- 9. Given non-negative real numbers $u, v, w$ satisfy $u+v+w=$ 2, then the range of $u^{2} v^{2}+v^{2} w^{2}+w^{2} u^{2}$ is $\qquad$ -/
theorem inequalities_285513 (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (h : u + v + w = 2) :
    0 ≤ u^2 * v^2 + v^2 * w^2 + w^2 * u^2 ∧ u^2 * v^2 + v^2 * w^2 + w^2 * u^2 ≤ 1 := by
  constructor
  · -- Proving that 0 is the lower bound is trivial
    positivity
  -- We assume WLOG that u is the max of u v w
  wlog u_max : w ≤ u ∧ v ≤ u generalizing u v w with h₁
  · rw [not_and_or, not_le, not_le] at u_max
    -- Assume WLOG v is the max of v w
    wlog v_max : w ≤ v generalizing u v w with h₂
    · rw [not_le] at v_max
      linarith [h₂ u w v hu hw hv (show u + w + v = 2 by linarith) (show u < v ∨ u < w by tauto) (show v ≤ w by linarith)]
    -- Show u ≤ v by simple casework on u_max
    have : u ≤ v := by
      rcases u_max with h' | h'
      · linarith
      linarith
    -- Conclude
    linarith [h₁ v u w hv hu hw (show v + u + w = 2 by linarith) ⟨v_max, this⟩]
  -- Have an inequality between v * w and 2 * u ^ 2
  have h₀ : v * w ≤ 2 * u ^ 2 := by nlinarith
  -- AM-GM inequality application
  have h₁ : u * (v + w) ≤ ((u + (v + w)) / 2) ^ 2 := by
    rw [div_pow]
    norm_num
    rw [le_div_iff₀ (by positivity)]
    -- Factor the inequality
    suffices 0 ≤ (u - (v + w)) ^ 2 by
      linarith
    -- Consequence of trivial inequality
    nlinarith
  calc
    -- Rewrite the expression to use h₀
    u^2 * v^2 + v^2 * w^2 + w^2 * u^2 = u^2 * (v + w)^2 + v * w * (v * w - 2 * u^2) := by ring
    -- Bound the negative term by zero
    _ ≤ u^2 * (v + w)^2 := by
      simp
      rw [mul_nonpos_iff]
      left
      exact ⟨by nlinarith, by linarith⟩
    _ = (u * (v + w)) ^ 2 := by rw [← mul_pow]
    -- Use h₁, aka AM-GM
    _ ≤ (((u + (v + w)) / 2) ^ 2) ^ 2 := by
      apply pow_le_pow_left₀
      · positivity
      tauto
    -- The resulting expression is just 1, as desired
    _ = (((u + v + w) / 2) ^ 2) ^ 2 := by rw [← add_assoc]
    _ = ((2 / 2) ^ 2) ^ 2 := by rw [h]
    _ = 1 := by norm_num