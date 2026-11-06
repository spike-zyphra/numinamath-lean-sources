import Mathlib

/- If $\sqrt{2\sqrt{t-2}} = \sqrt[4]{7 - t}$, then find $t$. -/
open Real in
theorem algebra_13576 : {t : ℝ | t - 2 ≥ 0 ∧ 7 - t ≥ 0 ∧ √(2 * √(t - 2)) = (7 - t) ^ ((1 : ℝ) / 4)} = {3} := by
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume t in the left side, prove t = 3
    rintro ⟨ht2, ht7, heq⟩
    -- Square both sides
    have h1 : (√(2 * √(t - 2))) ^ 2 = ( (7 - t) ^ ((1 : ℝ) / 4) ) ^ 2 := by
      rw [heq]
    -- Simplify left side
    have h2 : (√(2 * √(t - 2))) ^ 2 = 2 * √(t - 2) := by 
      rw [Real.sq_sqrt]
      positivity
    -- Simplify right side
    have h3 : ( (7 - t) ^ ((1 : ℝ) / 4) ) ^ 2 = (7 - t) ^ ((1 : ℝ) / 2) := by 
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      ring_nf
      all_goals linarith
    rw [h2, h3] at h1
    -- Now: 2 * √(t - 2) = (7 - t) ^ (1 / 2)
    -- Square both sides again
    have h4 : (2 * √(t - 2)) ^ 2 = ((7 - t) ^ ((1 : ℝ) / 2) ) ^ 2 := by 
      nlinarith [h1, Real.sqrt_nonneg (2 * Real.sqrt (t - 2)), Real.rpow_nonneg (show (7 - t : ℝ) ≥ 0 by linarith) (1 / 2)]
    -- Simplify left side
    have h5 : (2 * √(t - 2)) ^ 2 = 4 * (t - 2) := by
      calc
        (2 * √(t - 2)) ^ 2 = 4 * (√(t - 2) ^ 2) := by ring_nf
        _ = 4 * (t - 2) := by 
          rw [Real.sq_sqrt]
          linarith
    -- Simplify right side
    have h6 : ((7 - t) ^ ((1 : ℝ) / 2) ) ^ 2 = 7 - t := by 
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    rw [h5, h6] at h4
    -- Solve linear equation
    have ht3 : t = 3 := by
      nlinarith [h4]
    linarith
  · -- Now the reverse: if $t = 3$, then it is in the left set
    intro ht3
    rw [ht3]
    constructor
    · norm_num
    constructor 
    · norm_num
    · -- Verify the equation
      have h1 : √(2 * √(3 - 2 : ℝ)) = Real.sqrt 2 := by
        have h2 : (3 - 2 : ℝ) = (1 : ℝ) := by norm_num
        have h3 : Real.sqrt (3 - 2 : ℝ) = 1 := by
          rw [h2]
          exact Real.sqrt_one
        rw [h3]
        all_goals
          norm_num [Real.sqrt_mul_self]
      have h2 : ((7 - (3 : ℝ) ) ) ^ ((1 : ℝ) / 4) = Real.sqrt 2 := by
        have h3 : (7 - (3 : ℝ) ) = (4 : ℝ) := by norm_num
        rw [h3]
        have h4 : (4 : ℝ) ^ ((1 : ℝ) / 4) = Real.sqrt 2 := by 
          have h5 : (4 : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num]
            rw [← Real.rpow_mul]
            ring_nf
            all_goals norm_num
          have h6 : (2 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 2 := by
            rw [← Real.sqrt_eq_rpow]
          rw [h5, h6]
        exact h4
      rw [h1, h2]
      all_goals norm_num [Real.sqrt_nonneg]