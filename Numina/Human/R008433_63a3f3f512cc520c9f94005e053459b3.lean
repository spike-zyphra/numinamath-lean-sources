import Mathlib

/- What is the sum of the positive solutions to $2 x^{2}-x\lfloor x\rfloor=5$, where $\lfloor x\rfloor$ is the largest integer less than or equal to $x$ ?-/
theorem algebra_608727 :
    ∑ᶠ x ∈ {x : ℝ | 0 < x ∧ 2 * x ^ 2 - ⌊x⌋ * x = 5}, x = (3 + Real.sqrt 41 + 2 * Real.sqrt 11) / 4 := by
  -- It suffices to show that the solutions are only (1 + Real.sqrt 41) / 4 and (1 + Real.sqrt 11) / 2.
  suffices {x : ℝ | 0 < x ∧ 2 * x ^ 2 - ⌊x⌋ * x = 5} = {(1 + Real.sqrt 41) / 4, (1 + Real.sqrt 11) / 2} by
    -- Show that the two solutions are distinct.
    have h : (1 + Real.sqrt 41) / 4 ≠ (1 + Real.sqrt 11) / 2 := by
      -- Assume on the contrary that they are equal, we shall derive a contradiction.
      by_contra! h
      field_simp at h
      replace h : 4 * Real.sqrt 11 - 2 * Real.sqrt 41 = -2 := by
        linarith only [h]
      replace h := congr_arg (· ^ 2) h
      ring_nf at h
      field_simp at h
      rw [<-Real.sqrt_mul (by norm_num)] at h
      replace h : Real.sqrt (11 * 41) = 21 := by
        linarith only [h]
      rw [Real.sqrt_eq_iff_eq_sq] at h
      <;> norm_num
      norm_num at h
    rw [this, finsum_mem_eq_toFinset_sum]
    simp [h]
    linarith
  -- Break the goal into two parts.
  ext x
  simp
  apply Iff.intro
  . -- Show that the equation implies that x = (1 + √41) / 4 or (1 + √11) / 2.
    rintro ⟨hx, h₀⟩
    -- Show that x ^ 2 ≤ Real.sqrt 5 ^ 2.
    have h₁ : x ^ 2 ≤ Real.sqrt 5 ^ 2 := by
      calc
        _ = 2 * x ^ 2 - x ^ 2 := by ring
        _ ≤ 2 * x ^ 2 - ⌊x⌋ * x := by
          apply sub_le_sub_left
          rw [pow_two, mul_le_mul_iff_of_pos_right hx]
          apply Int.floor_le
        _ = Real.sqrt 5 ^ 2 := by
          field_simp [h₀]
    rw [sq_le_sq₀ (le_of_lt hx) (by positivity)] at h₁
    -- Let n = ⌊x⌋.
    let n := ⌊x⌋
    -- We have n < 3.
    have h₂ : n < 3 := by
      rify
      calc
        _ ≤ x := by apply Int.floor_le
        _ ≤ Real.sqrt 5 := h₁
        _ < 3 := by
          rw [Real.sqrt_lt]
          <;> norm_num
    -- We have n ≥ 0.
    have h₃ : 0 ≤ n := by
      rw [Int.le_floor]
      simp [le_of_lt hx]
    have hn : n = ⌊x⌋ := by rfl
    rw [show ⌊x⌋ = n by rfl] at h₀
    interval_cases n
    . -- Suppose n = 0, the equation becomes 2x² = 5.
      replace h₀ : x ^ 2 = 5 / 2 := by
        simp at h₀
        linarith only [h₀]
      -- However, this means that x ≥ 1, which is a contradiction.
      have : x ^ 2 ≥ 1 ^ 2 := by
        calc
          _ = 5 / 2 := h₀
          _ ≥ 1 ^ 2 := by norm_num
      rw [ge_iff_le, sq_le_sq₀ (by positivity) (le_of_lt hx)] at this
      rw [show (1 : ℝ) = (1 : ℤ) by simp, <-Int.le_floor, <-hn] at this
      norm_num at this
    . -- Suppose n = 1, the equation becomes 2x² - x = 5.
      replace h₀ : (4 * x - 1) ^ 2 = Real.sqrt 41 ^ 2 := by
        simp at h₀
        field_simp
        linarith only [h₀]
      have := Int.floor_le x
      simp [<-hn] at this
      rw [sq_eq_sq₀ (by linarith) (by norm_num)] at h₀
      -- We get the solution x = (1 + √41) / 4.
      left
      linarith
    . -- Suppose n = 2, the equation becomes 2x² - 2x = 5.
      replace h₀ : (2 * x - 1) ^ 2 = Real.sqrt 11 ^ 2 := by
        simp at h₀
        field_simp
        linarith only [h₀]
      have := Int.floor_le x
      simp [<-hn] at this
      rw [sq_eq_sq₀ (by linarith) (by norm_num)] at h₀
      -- We get the solution x = (1 + √11) / 2.
      right
      linarith
  . -- Show that the two values of x are indeed solutions.
    rintro (h₀ | h₀)
    . -- Show that (1 + √41) / 4 is a solution.
      have h₁ : ⌊x⌋ = 1 := by
        rw [Int.floor_eq_iff]
        -- Show that x is between 1 and 2.
        simp [h₀]
        refine ⟨?_, ?_⟩
        . linarith only [show 3 ≤ Real.sqrt 41 by rw [Real.le_sqrt] <;> norm_num]
        . linarith only [show Real.sqrt 41 < 7 by rw [Real.sqrt_lt] <;> norm_num]
      -- Show that the equation holds.
      rw [h₁, h₀]
      simp [show 0 < 1 + Real.sqrt 41 by positivity]
      ring_nf
      field_simp
      norm_num
    . -- Show that (1 + √11) / 2 is a solution.
      have h₁ : ⌊x⌋ = 2 := by
        rw [Int.floor_eq_iff]
        -- Show that x is between 2 and 3.
        simp [h₀]
        refine ⟨?_, ?_⟩
        . linarith only [show 3 ≤ Real.sqrt 11 by rw [Real.le_sqrt] <;> norm_num]
        . linarith only [show Real.sqrt 11 < 4 by rw [Real.sqrt_lt] <;> norm_num]
      -- Show that the equation holds.
      rw [h₁, h₀]
      simp [show 0 < 1 + Real.sqrt 11 by positivity]
      ring_nf
      field_simp
      norm_num
