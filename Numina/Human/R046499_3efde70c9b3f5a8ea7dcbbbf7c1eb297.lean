import Mathlib

/- Compute the smallest positive integer $n$ for which

$$
\sqrt{100+\sqrt{n}}+\sqrt{100-\sqrt{n}}
$$

is an integer.-/
theorem algebra_609882 :
    IsLeast {n : ℕ | 0 < n ∧ 100 - Real.sqrt n ≥ 0 ∧ ∃ m : ℕ, m = Real.sqrt (100 + Real.sqrt n) + Real.sqrt (100 - Real.sqrt n)} 6156 := by
  -- Simplify the goal into two parts.
  simp only [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- First show that 6156 indeed makes the expression integral.
    simp
    have : 100 - Real.sqrt 6156 ≥ 0 := by
      simp
      rw [Real.sqrt_le_iff]
      norm_num
    refine ⟨by simp_all, ?_⟩
    -- Let x = √(100 + √6156) + √(100 - √6156).
    let x : ℝ := Real.sqrt (100 + Real.sqrt 6156) + Real.sqrt (100 - Real.sqrt 6156)
    -- Show that x ^ 2 = 18 ^ 2.
    have h₀ : x ^ 2 = 18 ^ 2 := by
      simp [x, add_sq]
      field_simp
      ring_nf
      rw [<-Real.sqrt_mul (by positivity)]
      suffices (100 + Real.sqrt 6156) * (100 - Real.sqrt 6156) = 62 ^ 2 by
        field_simp [this]
        norm_num
      ring_nf
      field_simp
      norm_num
    rw [sq_eq_sq₀ (by positivity) (by norm_num)] at h₀
    use 18
    rify
    rw [<-h₀]
  . -- Show that n is at least 6156.
    simp only [Set.mem_setOf]
    rintro n ⟨h₀, h₁, m, h₂⟩
    -- Square both sides of h₂.
    replace h₂ := congr_arg (· ^ 2) h₂
    simp [add_sq] at h₂
    rw [mul_assoc, <-Real.sqrt_mul (by positivity), <-sq_sub_sq] at h₂
    field_simp at h₂
    ring_nf at h₂
    -- Note that m ^ 2 < 20 ^ 2.
    have h₃ : m ^ 2 < 20 ^ 2 := by
      rify
      calc
        _ = 200 + Real.sqrt (10000 - n) * 2 := h₂
        _ < 200 + 100 * 2 := by
          apply add_lt_add_left
          apply mul_lt_mul_of_pos_right
          . rw [Real.sqrt_lt]
            norm_num
            exact h₀
            -- Since √n ≤ 100, we have n ≤ 10000.
            simp at h₁ ⊢
            rw [Real.sqrt_le_iff] at h₁
            norm_num at h₁
            exact h₁
            norm_num
          . norm_num
        _ = 20 ^ 2 := by norm_num
    rw [Nat.pow_lt_pow_iff_left (by norm_num)] at h₃
    -- We elminate the case m = 19.
    have : m ≠ 19 := by
      by_contra!
      -- Assume on the contrary that m = 19, we prove a contradiction.
      simp [this] at h₂
      -- We have √(10000 - n) rational by the equation 19² = 200 + √(10000 - n) * 2.
      have h₅ : ¬Irrational (Real.sqrt (10000 - n : ℚ)) := by
        simp [Irrational]
        use 161 / 2
        linarith
      -- However, this shall implies that √(10000 - n) is an integer, which is not the case.
      rw [irrational_sqrt_ratCast_iff_of_nonneg, show (10000 - n : ℚ) = (10000 - n : ℤ) by simp, Rat.isSquare_intCast_iff] at h₅
      simp at h₅
      obtain ⟨m', h₅⟩ := h₅
      rify at h₅
      rw [h₅, <-pow_two, <-sq_abs (m' : ℝ), Real.sqrt_sq] at h₂
      norm_cast at h₂
      omega
      simp
      simp [Real.sqrt_le_iff] at h₁
      norm_num at h₁
      simp [h₁]
    -- Show that m ≤ 18.
    replace h₃ : m ≤ 18 := by
      omega
    clear this
    -- Show that √(10000 - ↑n) ≥ 62.
    rify at h₃
    rw [<-sq_le_sq₀ (by simp) (by norm_num)] at h₃
    replace h₂ : Real.sqrt (10000 - n) ≤ 62 := by
      linarith
    -- Show that n ≥ 6156.
    rw [Real.sqrt_le_iff] at h₂
    norm_num at h₂
    norm_cast at h₂
    omega

