import Mathlib

/- Solve for $x$ :

$$
x\lfloor x\lfloor x\lfloor x\lfloor x\rfloor\rfloor\rfloor\rfloor=122 .
$$-/
theorem number_theory_609825 :
    {x : ℝ | x * ⌊x * ⌊x * ⌊x * ⌊x⌋⌋⌋⌋ = 122} = {122 / 41} := by
  -- Simplify the goal into two parts.
  ext x
  simp
  apply Iff.intro
  . -- First show that the condition implies that x = 122 / 41.
    intro h₀
    -- First note that x ≥ 0.
    have h₁ : x > 0 := by
      -- Assume on the contrary that x ≤ 0, we know the left-hand side is non-positive.
      by_contra!
      -- First we have ⌊x⌋ ≤ 0.
      have h₁ : (⌊x⌋ : ℝ) ≤ 0 := by
        calc
          (⌊x⌋ : ℝ) ≤ x := by apply Int.floor_le
          _ ≤ 0 := this
      -- Then we have ⌊x * ⌊x⌋⌋ ≥ 0.
      have h₂ : 0 ≤ (⌊x * ⌊x⌋⌋ : ℝ) := by
        simp [Int.le_floor]
        apply mul_nonneg_of_nonpos_of_nonpos this h₁
      -- Then we have ⌊x * ⌊x * ⌊x⌋⌋⌋ ≤ 0.
      have h₃ : (⌊x * ⌊x * ⌊x⌋⌋⌋ : ℝ) ≤ 0 := by
        calc
          (⌊x * ⌊x * ⌊x⌋⌋⌋ : ℝ) ≤ x * ⌊x * ⌊x⌋⌋ := by apply Int.floor_le
          _ ≤ 0 := by
            apply mul_nonpos_of_nonpos_of_nonneg this h₂
      -- Then we have ⌊x * ⌊x * ⌊x * ⌊x⌋⌋⌋⌋ ≥ 0.
      have h₄ : 0 ≤ (⌊x * ⌊x * ⌊x * ⌊x⌋⌋⌋⌋ : ℝ) := by
        simp [Int.le_floor]
        apply mul_nonneg_of_nonpos_of_nonpos this h₃
      -- Then we have x * ⌊x * ⌊x * ⌊x * ⌊x⌋⌋⌋⌋ ≤ 0.
      have h₅ : (x * ⌊x * ⌊x * ⌊x * ⌊x⌋⌋⌋⌋ : ℝ) ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg this h₄
      -- This contradicts with our equation.
      linarith only [h₀, h₅]
    -- Let f(x) = x * ⌊x * ⌊x * ⌊x * ⌊x⌋⌋⌋⌋.
    let f : ℝ → ℝ := fun x => x * ⌊x * ⌊x * ⌊x * ⌊x⌋⌋⌋⌋
    -- Show that f is strictly increasing on [1, ∞).
    have h₂ (x y : ℝ) : 1 ≤ x → x < y → f x < f y := by
      -- A boring comparison of the two sides.
      intro hx hy
      simp [f]
      calc
        x * ⌊x * ⌊x * ⌊x * ⌊x⌋⌋⌋⌋ ≤ x * ⌊y * ⌊y * ⌊y * ⌊y⌋⌋⌋⌋ := by
          -- Repeatedly use the fact that x < y.
          rw [mul_le_mul_left (by linarith)]
          simp
          apply Int.floor_le_floor
          apply mul_le_mul (le_of_lt hy)
          . simp
            apply Int.floor_le_floor
            apply mul_le_mul (le_of_lt hy)
            . simp
              apply Int.floor_le_floor
              apply mul_le_mul (le_of_lt hy)
              . simp
                apply Int.floor_le_floor (le_of_lt hy)
              . positivity
              . linarith
            . simp
              positivity
            . linarith
          . simp
            positivity
          . linarith
        _ < y * ⌊y * ⌊y * ⌊y * ⌊y⌋⌋⌋⌋ := by
          rw [mul_lt_mul_right]
          exact hy
          -- Verify that 0 < ⌊y * ⌊y * ⌊y * ⌊y⌋⌋⌋⌋.
          suffices 1 ≤ ⌊y * ⌊y * ⌊y * ⌊y⌋⌋⌋⌋ by
            simp
            linarith
          simp [Int.le_floor]
          rw [show (1 : ℝ) = 1 * (1 : ℤ) by norm_num]
          apply mul_le_mul
          . linarith
          . norm_cast
            simp [Int.le_floor]
            rw [show (1 : ℝ) = 1 * (1 : ℤ) by norm_num]
            apply mul_le_mul
            . linarith
            . norm_cast
              simp [Int.le_floor]
              rw [show (1 : ℝ) = 1 * (1 : ℤ) by norm_num]
              apply mul_le_mul
              . linarith
              . norm_cast
                simp [Int.le_floor]
                linarith
              . norm_num
              . linarith
            . norm_num
            . linarith
          . norm_num
          . linarith
    -- Show that f(122 / 41) = 122.
    have h₃ : f (122 / 41) = 122 := by
      -- Direct calculations.
      norm_num [f]
    replace h₀ : f x = 122 := by
      simp [f, h₀]
    -- Show that x > 1 if f(x) = 122.
    replace h₁ : x > 1 := by
      by_contra!
      -- If otherwise, we can compare to get f(x) ≤ 1.
      have h₄ : f x ≤ 1 := by
        simp [f]
        rw [show (1 : ℝ) = 1 * (1 : ℤ) by norm_num]
        apply mul_le_mul this
        . refine (Int.floor_le (x * ⌊x * ⌊x * ⌊x⌋⌋⌋)).trans ?_
          norm_cast
          rw [show (1 : ℝ) = 1 * (1 : ℤ) by norm_num]
          apply mul_le_mul this
          . refine (Int.floor_le (x * ⌊x * ⌊x⌋⌋)).trans ?_
            norm_cast
            rw [show (1 : ℝ) = 1 * (1 : ℤ) by norm_num]
            apply mul_le_mul this
            . refine (Int.floor_le (x * ⌊x⌋)).trans ?_
              norm_cast
              rw [show (1 : ℝ) = 1 * (1 : ℤ) by norm_num]
              apply mul_le_mul this
              . refine (Int.floor_le x).trans ?_
                norm_cast
              . positivity
              . norm_num
            . positivity
            . norm_num
          . positivity
          . norm_num
        . positivity
        . norm_num
      linarith
    -- Show that x ≤ 122 / 41 and x ≥ 122 / 41.
    apply le_antisymm
    . by_contra!
      -- If not, then f(122 / 41) < f(x).
      specialize h₂ (122 / 41) x (by norm_num) this
      linarith
    . -- If not, then f(x) < f(122 / 41).
      by_contra!
      specialize h₂ x (122 / 41) (le_of_lt h₁) this
      linarith       
  . -- Show that 122 / 41 is indeed a solution.
    intro hx
    -- Direct calculations.
    norm_num [hx]