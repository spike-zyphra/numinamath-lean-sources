import Mathlib

open Real Set
open scoped BigOperators

/- The minimum positive period of the function $$y=\tan\left( \frac {\pi}{2}x- \frac {\pi}{3}\right)$$ is \_\_\_\_\_\_.
 -/
theorem algebra_9206 {f : ℝ → ℝ} (hf : f = λ x => tan (π/2 * x - π/3)) : IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} 2 := by
  rw [IsLeast]
  -- prove 2 is a positive period
  have hex: 2 ∈ {T | 0 < T ∧ f = fun x => f (x + T)} := by
    simp
    funext x
    rw [hf]
    simp
    have: π / 2 * (x + 2) - π / 3 = (π / 2 * x - π / 3) + π := by ring
    rw [this]
    symm
    exact (tan_add_pi (π / 2 * x - π / 3))
  -- prove 2 is a lower bound
  have hmin: 2 ∈ lowerBounds {T | 0 < T ∧ f = fun x => f (x + T)} := by
    rw [lowerBounds]
    simp
    intro T posT periodT
    by_contra! hc
    -- to argue about minimum positive period, we need find an interval such tat f(x) is injective
    have finj: InjOn f (Ioo (-1/3:ℝ) (5/3:ℝ)) := by
      rw [InjOn]
      intro x1 hx1 x2 hx2 feq
      rw [hf] at feq
      simp at feq
      -- to prove injectivity of tan, we try to transform it into arctan form.
      -- notice that we restrict x1 and x2 to such a region, that -π/2 < (π / 2 * x - π / 3) < π/2. because tan is injective on (-π/2, π/2)
      have h1: (π / 2 * x1 - π / 3) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        simp
        have ppos: 0 < π := by exact pi_pos
        rcases hx1 with ⟨h11, h22⟩
        have hl: π / 3 < π / 2 + π / 2 * x1 := by
          have: (-1/3:ℝ)*π  < x1 * π := by
            exact (mul_lt_mul_iff_of_pos_right ppos).mpr h11
          linarith [this]
        have hr: π / 2 * x1 - π / 3 < π / 2 := by
          have: π/2 * x1 < π/2 * (5/3) := by
            have: 0 < π /2 := by linarith [ppos]
            exact (mul_lt_mul_left this).mpr h22
          linarith [this]
        exact ⟨hl, hr⟩
      have h2: (π / 2 * x2 - π / 3) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        simp
        have ppos: 0 < π := by exact pi_pos
        rcases hx2 with ⟨h11, h22⟩
        have hl: π / 3 < π / 2 + π / 2 * x2 := by
          have: (-1/3:ℝ)*π  < x2 * π := by
            exact (mul_lt_mul_iff_of_pos_right ppos).mpr h11
          linarith [this]
        have hr: π / 2 * x2 - π / 3 < π / 2 := by
          have: π/2 * x2 < π/2 * (5/3) := by
            have: 0 < π /2 := by linarith [ppos]
            exact (mul_lt_mul_left this).mpr h22
          linarith [this]
        exact ⟨hl, hr⟩
      have feq': arctan (tan (π / 2 * x2 - π / 3)) = (π / 2 * x1 - π / 3) := by
        apply arctan_eq_of_tan_eq feq h1
      rcases h2 with ⟨hl, hr⟩
      rw [arctan_tan hl hr] at feq'
      have ht1: π / 2 * x2 = π /2 * x1 := by
        have: π / 2 * x2 = π / 2 * x2 - π/3 + π/3 := by ring
        rw [this, feq']
        ring
      have ht2: π / 2 * (x2 - x1) = 0 := by
        have: π / 2 * (x2 - x1) = π /2 * x2 - π /2 * x1 := by ring
        rw [this, ht1]
        ring
      have: π /2 ≠ 0 := by linarith
      have: x2 - x1 = 0 := by
        exact eq_zero_of_ne_zero_of_mul_left_eq_zero this ht2
      linarith [this]
    -- now, use f(x)=f(x+T) and T<2 to get a contradiction
    have feq: f (-1/3+(2-T)/2) = f (T/2+2/3) := by
      have: T/2+2/3 = (-1/3+(2-T)/2) + T := by ring
      rw [this]
      nth_rw 1 [periodT]
    have h1: -1/3+(2-T)/2 ∈ Ioo (-1 / 3) (5 / 3) := by
      simp
      have: -1 / 3 + (2 - T) / 2 < 5 / 3 := by linarith
      exact ⟨hc, this⟩
    have h2: T/2+2/3 ∈ Ioo (-1 / 3) (5 / 3) := by
      simp
      have hl: -1 / 3 < T / 2 + 2 / 3 := by linarith
      have hr: T / 2 + 2 / 3 < 5 / 3 := by linarith
      exact ⟨hl,hr⟩
    have eq: -1 / 3 + (2 - T) / 2 = T / 2 + 2 / 3 := by
      apply finj h1 h2 feq
    -- from eq, we can solve T=-1/6
    -- however, we assume T is positive. contradiction
    have negT: T < 0 := by linarith [eq]
    linarith [posT, negT]
  exact ⟨hex,hmin⟩