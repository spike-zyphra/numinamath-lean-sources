import Mathlib

open Real Set
open scoped Real

/- Let $\alpha$ and $\beta$ be angles for which
\[\frac{\sec^4 \alpha}{\tan^2 \beta} + \frac{\sec^4 \beta}{\tan^2 \alpha}\]is defined.  Find the minimum value of the expression. -/
theorem calculus_23329{sec: ℝ → ℝ}(hsec: ∀α:ℝ, sec α = 1 / (cos α)) :
  IsLeast {x : ℝ | ∃ α β, x = (sec α)^4 / (tan β)^2 + (sec β)^4 / (tan α)^2 ∧ cos α ≠ 0 ∧ cos β ≠ 0 ∧ tan α ≠ 0 ∧ tan β ≠ 0} 8 := by
  -- sec θ stands for secant θ, and is defined to be 1/cosθ
  -- when cosθ=0, secθ and tanθ are undefined. so cosα, cosβ are nonzero. and tanα,tanβ are on the denominator, also nonzero.
  rw [IsLeast, lowerBounds]; simp
  constructor
  -- later we will prove why reach minimum at π/4. in this direction, we just verify the answer π/4.
  · use (π/4); use (π/4)
    rw [hsec]; simp; ring_nf
    have: √2^4 = 4 := by
      have: √2^4 = (√2^2)^2 := by ring
      rw [this]; simp; ring
    rw [this]; ring
  · -- in this direction, we will find the minimum of (secα)^4/(tanβ)^2 + (secα)^4/(tanβ)^2. to simplify, let a =(tanα)^2 and b=(tanβ)^2
    intro x α β hx nza nzb nza' nzb'
    let a := (tan α)^2
    have a_def: a = (tan α)^2 := rfl
    have a_nonneg: 0 ≤ a := sq_nonneg (tan α)
    let b := (tan β)^2
    have b_def: b = (tan β)^2 := rfl
    have b_nonneg: 0 ≤ b := sq_nonneg (tan β)
    -- notice that (secθ)^2 = 1 + (tanθ)^2
    have hsec2'(θ)(nz: cos θ ≠ 0): (sec θ)^2 = 1 + (tan θ)^2 := by
      have: tan θ = sin θ / cos θ := tan_eq_sin_div_cos θ
      rw [this, hsec]
      field_simp [nz]
    have hsec2(θ)(nz:cos θ ≠ 0): (sec θ)^4 = (1+(tan θ)^2)^2 := by
      rw [← hsec2' θ nz]; ring
    -- therefore, the original expression turns to be (a+1)^2/b + (b+1)^2/a
    have h1: (sec α)^4/(tan β)^2 + (sec β)^4/(tan α)^2 =
      (a+1)^2/b + (b+1)^2/a := by
      rw [hsec2 α nza, hsec2 β nzb, ← a_def, ← b_def]; ring
    -- notice that by AM-GM, a+1 ≥ 2√a.
    have ineq_aux1(y:ℝ)(ynonneg: 0 ≤ y): y+1 ≥ 2*√y := by
      have hh1: 2*√y ≤ (√y)^2 + 1^2 := by
        have: 2*√y = 2*√y*1 := by ring
        rw [this]
        exact two_mul_le_add_sq (√y) 1
      have hh2: y+1 = (√y)^2 + 1^2 := by
        have: y = (√y)^2 := by
          symm; apply sq_sqrt ynonneg
        rw [← this]; ring
      rwa [← hh2] at hh1
    -- therefore, (a+1)^2 ≥ 4a, (b+1)^2 ≥ 4b. and following holds.
    have ineq1: (a+1)^2/b + (b+1)^2/a ≥ 4 * (b/a + a/b) := by
      by_cases az: a = 0; rw [az]; simp [b_nonneg]
      by_cases bz: b = 0; rw [bz]; simp [a_nonneg]
      have apos: 0 < a := by
        push_neg at az
        apply lt_of_le_of_ne a_nonneg az.symm
      have bpos: 0 < b := by
        push_neg at bz
        apply lt_of_le_of_ne b_nonneg bz.symm
      have hh1(c:ℝ)(cpos: 0 < c): (c+1)^2 ≥ 4*c := by
        have: 4*c = (2*√c)^2 := by
          have: c = (√c)^2 := by
            symm; apply sq_sqrt (le_of_lt cpos)
          nth_rw 1 [this]
          ring
        rw [this]
        apply sq_le_sq'
        · have: -(c+1) ≤ 0 := by linarith [cpos]
          apply le_trans this
          have: 0 ≤ √c := sqrt_nonneg c
          linarith [this]
        · apply ineq_aux1 c (le_of_lt cpos)
      have hh2: (a+1)^2/b ≥ 4*a/b := by
        have := hh1 a apos
        apply div_le_div_of_nonneg_right this b_nonneg
      have hh3: (b+1)^2/a ≥ 4*b/a := by
        have := hh1 b bpos
        apply div_le_div_of_nonneg_right this a_nonneg
      have hh4: 4*(b/a+a/b) = 4*a/b + 4*b/a := by ring
      rw [hh4]
      linarith [hh2, hh3]
    -- notice that b/a+a/b ≥ 2. because by AM-GM, (√(b/a))^2 + (√(a/b))^2 ≥ 2*√(b/a)*√(a/b)
    have ineq2(ha: a ≠ 0)(hb: b ≠ 0): b/a+a/b ≥ 2 := by
      have ba_nonneg: 0 ≤ b/a := by
        exact div_nonneg b_nonneg a_nonneg
      have ab_nonneg: 0 ≤ a/b := by
        exact div_nonneg a_nonneg b_nonneg
      have hh1: b/a = √(b/a)^2 := by
        exact Eq.symm (sq_sqrt ba_nonneg)
      have hh2: a/b = √(a/b)^2 := by
        exact Eq.symm (sq_sqrt ab_nonneg)
      have hh3: 2 = 2 * √(b/a) * √(a/b) := by
        field_simp [ha, hb]
      rw [hh1, hh2, hh3]
      exact two_mul_le_add_sq √(b / a) √(a / b)
    have ineq3(ha: a ≠ 0)(hb: b ≠ 0): 4*(b/a+a/b) ≥ 8 := by
      have: (8:ℝ) = 4*2 := by norm_num
      rw [this]
      linarith [ineq2 ha hb]
    -- thus we nearly finish. notice we use (a+1)^2 ≥ 2√a, equal sign takes when a=1. and for b/a+a/b ≥ 2, equal sign takes when a=b. so when a=b=1, or α = β = π /4, reach the minimum.
    rw [hx, h1]
    refine le_trans (ineq3 ?_ ?_) ineq1
    · rw [a_def]; push_neg at nza'; exact pow_ne_zero 2 nza'
    · rw [b_def]; push_neg at nzb'; exact pow_ne_zero 2 nzb'