import Mathlib

open Real Set
open scoped Real
/-
5. The solution set of the equation $4 \sin x(1+\cos x)=3 \sqrt{3}$ is
-/
theorem algebra_325715:
  {x : ℝ | 4 * sin x * (1 + cos x) = 3 * sqrt 3} = {x | ∃(k:ℤ), x = 2*k*π + π/3 } := by
  ext x
  apply Iff.intro
  · -- the forward direction
    intro hx; simp_all
    -- squaring both side of hx
    have hx' := congrArg (·^2) hx
    -- we get  (4 * sin x * (1 + cos x)) ^ 2 = (3 * √3) ^ 2
    simp at hx'
    -- calculation of (3 * √3) ^ 2
    have: (3 * √3)^2 = 27 := by 
      ring_nf
      rw [Real.sq_sqrt (by simp)]
      norm_cast
    -- next the equation becomes (4 * sin x * (1 + cos x)) ^ 2 -27 = 0
    rw [this, <-sub_eq_zero] at hx'; clear this
    -- we next show that (4 * sin x * (1 + cos x)) ^ 2 -27 = -(2*cos x - 1)^2*(4* (cos x)^2 + 12 * cos x + 11)
    have h_eq: (4 * sin x * (1 + cos x)) ^ 2 -27 = 
          -(2*cos x - 1)^2*(4* (cos x)^2 + 12 * cos x + 11) := by
      -- the key is to convert sin x^2 to cos x^2
      have h_sin_sq_eq: (sin x)^2 = 1-(cos x)^2 := by
        rw [<-Real.sin_sq_add_cos_sq (x := x), <-add_sub]
        simp
      -- by expanding the power, we can now rewrite (sin x)^2
      rw [mul_pow, mul_pow, h_sin_sq_eq]
      -- now the goal only involves powers of cos x, hence we use ring_nf to prove the goal
      ring_nf
    -- substituting h_eq into hx', we get 2 * cos x - 1 = 0 ∨ 4 * cos x ^ 2 + 12 * cos x + 11 = 0
    simp [h_eq] at hx'
    clear h_eq
    rcases hx' with hx' | hx'
    · -- case 1: 2 * cos x - 1 = 0, then cos x = 1 / 2
      have h': cos x = 1 / 2 := by
        rw [sub_eq_zero, mul_comm] at hx'
        have hx'' := eq_div_of_mul_eq (c := (2:ℝ)) (by simp) hx'
        exact hx''
      have h'' := h'
      -- apparently cos π / 3 = 1/2, and we can extend it to other intervals
      rw [<-Real.cos_pi_div_three] at h'
      symm at h'
      rw [Real.cos_eq_cos_iff] at h'
      obtain ⟨k, hk⟩ := h'
      rcases hk with hk|hk
      · -- case 1. 2kπ + π /3
        use k
      · -- case 2. we show that sin x will be ngative
        have h_sin: sin x = - Real.sqrt 3 / 2 := by
          rw [hk, mul_comm (a := 2), mul_assoc]
          simp
          field_simp
        -- rewriting cos x and sin x in the original equation, it is incorrect
        rw [h'', h_sin] at hx
        exfalso
        ring_nf at hx
        -- we are left with hx : -(√3 * 3) = √3 * 3 which is impossible.
        rw [<-add_right_inj (√3 * 3), add_neg_cancel] at hx
        ring_nf at hx
        simp at hx
    · -- case 2: 4 * cos x ^ 2 + 12 * cos x + 11 = 0
      generalize hc: cos x = c at hx'
      -- we have the quadratic equation where 4*c^2 + 12*c + 11 = 0 which has no real solution
      have : 4*c^2 + 12*c + 11 ≠ 0 := by
        rw [pow_two]
        apply quadratic_ne_zero_of_discrim_ne_sq
        -- Δ = 12*12 - 4 * 4 * 11 < 0
        unfold discrim
        -- to show that, assume 12*12 - 4 * 4 * 11 = s ^2 for some s
        intro s H
        -- s^2 is nonnegative
        have h_sq_nonneg := sq_nonneg s
        -- hence 12*12 - 4 * 4 * 11 >= 0 which is a contradiction
        rw [<-H] at h_sq_nonneg
        linarith
      simp [hx'] at this
  · -- the backward direction, we can simply verify the equation
    intro hx; simp_all
    -- for cos π / 3
    have h_cos_pi_div_3 := Real.cos_pi_div_three
    obtain ⟨k, hx⟩ := hx
    -- and we convert x's into π /3
    have h_cos: cos x = 1 / 2 := by
      -- we show that cos x = cos (2kπ + π/3) = cos (π/3 + k *(2*π))
      rw [hx, mul_comm (a := 2), mul_assoc, add_comm]
      simp
    -- for sin π / 3
    have h_sin: sin x = √3 / 2 := by
      rw [hx, mul_comm (a := 2), mul_assoc, add_comm]
      simp
    -- now we put these values back to the original equation
    rw [h_cos, h_sin]
    ring


      
      
      



