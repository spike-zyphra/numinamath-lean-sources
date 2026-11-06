import Mathlib

/- For example. Solve the equation: $\sqrt{x+3}+\sqrt{2 x-1}=4$.-/
theorem algebra_325086 :
    {x : ℝ | 0 ≤ x + 3 ∧ 0 ≤ 2 * x - 1 ∧ Real.sqrt (x + 3) + Real.sqrt (2 * x - 1) = 4} = {52 - 8 * Real.sqrt 39} := by
  ext x
  constructor
  · -- Assume √(x + 3) + √(2x - 1) = 4, prove that x = 52 - 8√39.
    rintro ⟨h₀, h₁, h₂⟩
    -- Square both sides of h₂.
    have h₃ := congr_arg (· ^ 2) h₂
    simp [add_sq] at h₃
    field_simp at h₃
    rw [mul_assoc, <-Real.sqrt_mul (by positivity)] at h₃
    -- Change the equation to 2√((x + 3) * (2 * x - 1)) = -3x + 14.
    replace h₃ : 2 * √((x + 3) * (2 * x - 1)) = -3 * x + 14 := by
      linarith only [h₃]
    -- Square both sides of h₃.
    replace h₃ := congr_arg (· ^ 2) h₃
    field_simp [mul_pow] at h₃
    ring_nf at h₃
    -- We change the equation to (x - 52)² - 2496 = x² - 104x + 208 = 0.
    replace h₃ : (x - 52) ^ 2 = Real.sqrt 2496 ^ 2 := by
      norm_num
      linarith only [h₃]
    rw [sq_eq_sq_iff_eq_or_eq_neg] at h₃
    rcases h₃ with (h₃ | h₃)
    . -- Case x - 52 = √2496, not satisfying the original equation.
      absurd h₂
      -- Show that 4 < √(x + 3) + √(2x - 1).
      apply ne_of_gt
      calc
        4 < Real.sqrt (x + 3) := by
          rw [Real.lt_sqrt (by norm_num)]
          linarith only [h₃, show 0 ≤ Real.sqrt 2496 by norm_num]
        _ ≤ Real.sqrt (x + 3) + Real.sqrt (2 * x - 1) := by
          linarith only [Real.sqrt_nonneg (2 * x - 1)]
    . -- Case x - 52 = -√2496, corresponding to the solution we want.
      rw [show (2496 : ℝ) = 8 ^ 2 * 39 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)] at h₃
      simp
      linarith only [h₃]
  . -- Now we prove that x = 52 - 8√39 does satisfy the original equation.
    intro hx
    simp at hx
    -- Show that 0 ≤ 2x - 1.
    have h₀ : 0 ≤ 2 * x - 1 := by
      rw [hx]
      ring_nf
      rw [le_sub_iff_add_le, add_comm, <-le_sub_iff_add_le]
      -- Square both sides.
      rw [<-sq_le_sq₀ (by norm_num) (by norm_num), mul_pow]
      norm_num
    -- Show that 0 ≤ x + 3.
    have h₁ : 0 ≤ x + 3 := by
      linarith only [h₀]
    -- It remains to show that √(x + 3) + √(2x - 1) = 4.
    refine ⟨h₁, h₀, ?_⟩
    -- Square both sides to try to get rid of square roots.
    rw [<-sq_eq_sq₀ (by positivity) (by norm_num)]
    simp [add_sq]
    field_simp
    rw [mul_assoc, <-Real.sqrt_mul h₁]
    apply add_eq_of_eq_sub
    rw [add_comm]
    apply add_eq_of_eq_sub
    -- Show that (2x - 1) + (x + 3) ≤ 16.
    have h₂ : (2 * x - 1) + (x + 3) ≤ 16 := by
      rw [hx]
      ring_nf
      rw [sub_le_iff_le_add, add_comm, <-sub_le_iff_le_add]
      -- Square both sides.
      rw [<-sq_le_sq₀ (by norm_num) (by positivity), mul_pow]
      norm_num
    -- Square both sides again.
    rw [<-sq_eq_sq₀ (by positivity) (by linarith only [h₂]), mul_pow, Real.sq_sqrt (by positivity)]
    -- Now it suffices to show that (x - 52)² = 2496.
    suffices (x - 52) ^ 2 = 2496 by
      linarith
    field_simp [hx, mul_pow]
    norm_num
