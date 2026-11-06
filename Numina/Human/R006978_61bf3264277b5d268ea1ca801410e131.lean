import Mathlib

/- Find the largest real number $\alpha$ such that, for all non-negative real numbers $x, y$ and $z$, the following inequality holds:

$$
(x+y+z)^{3}+\alpha\left(x^{2} z+y^{2} x+z^{2} y\right) \geq \alpha\left(x^{2} y+y^{2} z+z^{2} x\right) .
$$

Answer: $6 \sqrt{3}$. -/
theorem inequalities_605091 :
    IsGreatest {α : ℝ | ∀ x y z : ℝ, x ≥ 0 → y ≥ 0 → z ≥ 0 → (x + y + z) ^ 3 + α * (x ^ 2 * z + y ^ 2 * x + z ^ 2 * y) ≥ α * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x)} (6 * Real.sqrt 3) := by
  -- Simplify the goal intwo two parts.
  simp [IsGreatest, upperBounds]
  refine ⟨?_, ?_⟩
  . -- First show that 6√3 satisfies the condition.
    intro x y z hx hy hz
    -- First show that (x + y + z)³ ≥ 6√3|x - y||y - z||z - x|.
    have h₀ : (x + y + z) ^ 3 ≥ 6 * Real.sqrt 3 * |x - y| * |y - z| * |z - x| := by
      -- WLOG, assume that x ≥ y.
      wlog hxy : x ≥ y
      . -- Prove that the other cases is similar.
        simp at hxy
        specialize this y x z hy hx hz (le_of_lt hxy)
        nth_rw 1 [<-neg_sub] at this
        nth_rw 2 [<-neg_sub] at this
        nth_rw 3 [<-neg_sub] at this
        iterate 3 rw [abs_neg] at this
        linarith only [this]
      . -- WLOG, assume that y ≥ z.
        wlog hyz : y ≥ z
        . -- Prove that other cases are similar.
          simp at hyz
          by_cases hxz : x ≥ z
          . specialize this x z y hx hz hy hxz (le_of_lt hyz)
            nth_rw 1 [<-neg_sub] at this
            nth_rw 2 [<-neg_sub] at this
            nth_rw 3 [<-neg_sub] at this
            iterate 3 rw [abs_neg] at this
            linarith only [this]
          . simp at hxz
            specialize this z x y hz hx hy (le_of_lt hxz) hxy
            linarith only [this]
        . -- It suffices to show that (x + y + z)³ ≥ 6√3(x - y)(y - z)(x - z).
          have h₁ : 0 ≤ x - y := by
            linarith only [hxy]
          have h₂ : 0 ≤ y - z := by
            linarith only [hyz]
          have h₃ : 0 ≤ x - z := by
            linarith only [h₁, h₂]
          rw [abs_of_nonneg h₁, abs_of_nonneg h₂, <-neg_sub x z, abs_neg, abs_of_nonneg h₃]
          -- It suffices to show that x + y + z ≥ 3(2√3 / 9 * (x - y) * (y - z) * (x - z)) ^ (1 / 3).
          suffices x + y + z ≥ 3 * ((2 * Real.sqrt 3) / 9 * ((x - y) * (y - z) * (x - z))) ^ (1 / 3 : ℝ) by
            rw [ge_iff_le] at this ⊢
            have := pow_le_pow_left₀ (by positivity) this 3
            rw [<-Real.rpow_natCast, Real.mul_rpow (by norm_num) (by positivity), <-Real.rpow_mul (by positivity)] at this
            norm_num at this
            linarith only [this]
          calc
            x + y + z ≥ x + y - 2 * z := by linarith
            _ = Real.sqrt 3 / 3 * (x - y) + (3 + Real.sqrt 3) / 3 * (y - z) + (3 - Real.sqrt 3) / 3 * (x - z) := by ring
            _ ≥ 3 * ((2 * Real.sqrt 3) / 9 * ((x - y) * (y - z) * (x - z))) ^ (1 / 3 : ℝ) := by
              -- Prove the AM-GM inequality for three variables.
              have AM_GM_ineq (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (1 / 3 : ℝ) * x + (1 / 3 : ℝ) * y + (1 / 3 : ℝ) * z ≥ x ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ) * z ^ (1 / 3 : ℝ) := by
                apply Real.geom_mean_le_arith_mean3_weighted (by norm_num) (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity) (by norm_num)
              have : 0 ≤ 3 - Real.sqrt 3 := by
                simp
                rw [Real.sqrt_le_iff]
                norm_num
              -- Apply the AM-GM inequality.
              specialize AM_GM_ineq (Real.sqrt 3 / 3 * (x - y)) ((3 + Real.sqrt 3) / 3 * (y - z)) ((3 - Real.sqrt 3) / 3 * (x - z)) (by positivity) (by positivity) (by positivity)
              rw [<-Real.mul_rpow (by positivity) (by positivity), <-Real.mul_rpow (by positivity) (by positivity)] at AM_GM_ineq
              replace this : (Real.sqrt 3 / 3 * (x - y)) * ((3 + Real.sqrt 3) / 3 * (y - z)) * ((3 - Real.sqrt 3) / 3 * (x - z)) = (2 * Real.sqrt 3) / 9 * ((x - y) * (y - z) * (x - z)) := by
                calc
                  (Real.sqrt 3 / 3 * (x - y)) * ((3 + Real.sqrt 3) / 3 * (y - z)) * ((3 - Real.sqrt 3) / 3 * (x - z))
                  _ = (Real.sqrt 3 / 3) * ((3 + Real.sqrt 3) / 3) * ((3 - Real.sqrt 3) / 3) * ((x - y) * (y - z) * (x - z)) := by ac_rfl
                  _ = (2 * Real.sqrt 3) / 9 * ((x - y) * (y - z) * (x - z)) := by
                    congrm ?_ * ?_
                    . field_simp
                      rw [mul_assoc, mul_assoc, <-mul_assoc _ _ 9, <-sq_sub_sq, Real.sq_sqrt (by norm_num)]
                      ring
                    . rfl
              -- Simplify to get the desired inequality.
              rw [this] at AM_GM_ineq
              clear this
              linarith only [AM_GM_ineq]
    rw [<-neg_sub x z, abs_neg] at h₀
    -- We have (x + y + z)³ ≥ 6√3(x - y)(y - z)(x - z).
    have h₁ : (x + y + z) ^ 3 ≥ 6 * Real.sqrt 3 * (x - y) * (y - z) * (x - z) := by
      calc
        (x + y + z) ^ 3 ≥ 6 * Real.sqrt 3 * |x - y| * |y - z| * |x - z| := h₀
        _ ≥ 6 * Real.sqrt 3 * (x - y) * (y - z) * (x - z) := by
          -- Use the fact that absolute value is greater than or equal to the value inside.
          rw [mul_assoc, mul_assoc, <-abs_mul, <-abs_mul, ge_iff_le, mul_assoc, mul_assoc, mul_le_mul_left (by positivity)]
          apply le_abs_self
    -- The original inequality with α = 6√3 is just a rearrangement of terms.
    linarith only [h₁]
  . -- Show that 6√3 is the greatest possible value of α.
    intro α h
    -- Substitute (x, y, z) = (2 + √3, 1, 0).
    specialize h (2 + Real.sqrt 3) 1 0 (by positivity) (by norm_num) (by norm_num)
    ring_nf at h
    rw [show Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 by ring] at h
    repeat rw [Real.sq_sqrt (by norm_num)] at h
    rw [<-sub_nonneg] at h
    ring_nf at h
    -- The result is equivalent to a direct scalar multiplication of h.
    rw [<-mul_le_mul_right (show 0 < 5 + Real.sqrt 3 * 3 by positivity)]
    nth_rw 2 [mul_add, mul_assoc]
    rw [<-mul_assoc _ _ 3, <-pow_two, Real.sq_sqrt (by norm_num)]
    linarith only [h]
