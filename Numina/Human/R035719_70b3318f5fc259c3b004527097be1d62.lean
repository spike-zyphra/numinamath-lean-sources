import Mathlib

open Real Set
open scoped Real

/- Solve $\arcsin x + \arcsin (1 - x) = \arccos x.$ -/
theorem calculus_16672 {x : ℝ} (hx : x ∈ Icc 0 1) :
  arcsin x + arcsin (1 - x) = arccos x ↔ x = 0 ∨ x = 1 / 2 := by
  obtain ⟨hxge, hxle⟩ := hx
  have x1ge: -1 ≤ 1-x := by linarith [hxle]
  have x1le: 1-x ≤ 1 := by linarith [hxge]
  constructor <;> intro h
  -- take sin of both sides
  · have h1: sin (arcsin x + arcsin (1-x)) = sin (arccos x) := by
      rw [h]
    -- notice that sin (A+B) = sinAcosB + sinBcosA
    rw [Real.sin_add] at h1
    -- simplify
    have ht1: sin (arcsin x) = x := by
      rw [sin_arcsin (by linarith [hxge]) hxle]
    have ht2: sin (arcsin (1-x)) = 1- x := by
      rw [sin_arcsin x1ge x1le]
    have ht3: cos (arcsin (1-x)) = √(1-(1-x)^2) := by
      have: cos (arcsin (1-x)) = √(1-(sin (arcsin (1-x)))^2) := by
        rw [sin_sq]; simp
        have: 0 ≤ cos (arcsin (1-x)) := cos_arcsin_nonneg (1-x)
        symm; exact sqrt_sq this
      rw [this, ht2];
    have ht4: cos (arcsin x) = √(1-x^2) := by
      rw [← ht1, sin_sq]; simp; rw [sin_arcsin (by linarith [hxge]) hxle]
      symm; refine sqrt_sq ?_
      exact cos_arcsin_nonneg x
    rw [ht1, ht2, ht3, ht4, sin_arccos] at h1
    -- then we get x√(1-(1-x)^2)+√(1-x^2)(1-x)=√(1-x^2)
    have h2: x*√(1-(1-x)^2) = x*√(1-x^2) := by linarith [h1]
    -- square both sides
    have h3: x^2 * (1-(1-x)^2) = x^2*(1-x^2) := by
      have ht1: x^2*(1-x^2) = (x*√(1-x^2))^2 := by
        have: (√(1-x^2))^2 = 1-x^2 := by
          have: x^2 ≤ 1 := by
            exact (sq_le_one_iff hxge).mpr hxle
          apply sq_sqrt (by linarith [this])
        ring_nf; simp[this]; ring
      have ht2: (√(x*2-x^2))^2 = x*2 - x^2 := by
        apply sq_sqrt
        have hh1: x*2-x^2 = 1-(1-x)^2 := by ring
        have hh2: (1-x)^2 ≤ 1 := by
          have: 0 ≤ 1-x := by linarith [hxle]
          apply (sq_le_one_iff this).mpr x1le
        rw [hh1]; linarith [hh2]
      rw [ht1, ← h2]; ring_nf; rw [ht2]; ring
    -- and that simplifies to x^2(2*x-1) = 0
    have h4: x^2 * (2*x-1) = 0 := by
      have: x^2 * (2*x-1) =
        x^2 * (1-(1-x)^2) - x^2 * (1-x^2) := by ring
      rw [this, h3]; ring
    -- so either x^2 = 0 (leads to x=0) or 2x-1 = 0
    have h5 := mul_eq_zero.mp h4
    rcases h5 with h0 | h12
    · left; rw [pow_two] at h0; have := mul_eq_zero.mp h0; tauto
    · right; linarith [h12]
  -- and now we verify x=0, x=1/2 are two solutions for the equation
  · rcases h with h0 | h12
    · rw [h0]; simp
    -- notice that arcsin 1/2 = π/6 and arccos 1/2 = π/3
    · have ht1: arcsin (1/2) = π/6 := by
        have: sin (π/6) = 1/2 := by
          exact sin_pi_div_six
        rw [← this]
        apply arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])
      have ht2: arccos (1/2) = π/3 := by
        have: cos (π/3) = 1/2 := by
          exact cos_pi_div_three
        rw [← this]
        apply arccos_cos (by linarith [pi_pos]) (by linarith [pi_pos])
      have ht3: 1-x = 1/2 := by rw [h12]; ring
      rw [ht3, h12, ht1, ht2]; ring