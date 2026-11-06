import Mathlib

open Real

/-Given that $a$ and $b$ are real numbers, if for any $x\in R$, $\left(\ln a+b\right)e^{x}-a^{2}ex\geqslant 0$ always holds, then the minimum value of $\frac{b}{a}$ is ____.-/
theorem algebra_9126_1 (a b : ℝ) (ha : 0 < a)
(h : ∀ x : ℝ, (Real.log a + b) * Real.exp x - a ^ 2 * rexp 1 * x ≥ 0) :
b / a ≥ 1 := by
-- Plug in $x=1$ to the assumption to get an inequality on $a$ and $b$
  have h1 := h 1; simp at h1; rw [mul_le_mul_right] at h1
  rw [← sub_le_iff_le_add'] at h1
  replace h1 := div_le_div_of_nonneg_right h1 (show 0≤a by linarith)
  have lm1 : ∀ x, 0 < x → 1 ≤ (x ^ 2- Real.log x) / x := by
    let f := (λ x => (x ^ 2 - Real.log x) / x)

-- Prove $f$ is continuous when $x$ is positive
    have hf0 : ∀ x, 0 < x → ContinuousAt f x := by
      intro x hx; simp [f]; apply ContinuousAt.div
      apply ContinuousAt.sub; apply ContinuousAt.pow
      apply continuousAt_id'; apply continuousAt_log; linarith
      apply continuousAt_id'; linarith

-- Prove $f$ is differentiable when $x$ is positive
    have h'f0 : ∀ x, 0 < x → DifferentiableAt ℝ f x := by
      intro x hx; simp [f]; apply DifferentiableAt.div
      apply DifferentiableAt.sub; apply DifferentiableAt.pow
      simp; simp; linarith; simp; linarith

-- Compute the derivative of $f$
    have derf : ∀ x, 0 < x → deriv f x = (x ^ 2 - 1 + log x) / x ^ 2 := by
      intro x hx; simp [f]; rw [deriv_div]
      rw [deriv_sub]; simp; field_simp; ring
      apply DifferentiableAt.pow; simp; simp; linarith
      apply DifferentiableAt.sub; apply DifferentiableAt.pow
      simp; simp; linarith; simp; linarith

-- Define another function $g$ for later use
    let g := λ x => x ^ 2 - 1 + log x

-- Prove $g$ is continuous
    have contg : ∀ x, 0 < x → ContinuousAt g x := by
      intro x hx; simp [g]; apply ContinuousAt.add
      apply ContinuousAt.sub; apply ContinuousAt.pow
      apply continuousAt_id'; apply continuousAt_const
      simp; linarith

-- Prove $g$ is differentiable
    have diffg : ∀ x, 0 < x → DifferentiableAt ℝ g x := by
      intro x hx; simp [g]; linarith

-- Compute the derivative of $g$
    have hg0 : ∀ x, 0 < x → deriv g x = 2 * x + 1 / x := by
      intro x hx; rw [deriv_add]; simp
      apply DifferentiableAt.sub; apply DifferentiableAt.pow
      simp; simp; simp; linarith

-- Prove that $g$ is monotone when $x$ is positive
    have h'g0 : MonotoneOn g (Set.Ioi 0) := by
      apply monotoneOn_of_deriv_nonneg; apply convex_Ioi
      rw [ContinuousOn]; intro x hx; simp at hx
      apply ContinuousAt.continuousWithinAt; apply contg
      assumption; simp; rw [DifferentiableOn]
      intro x hx; simp at hx
      apply DifferentiableAt.differentiableWithinAt
      apply diffg; assumption
      intro x hx; simp at hx; rw [hg0]; apply add_nonneg
      linarith; rw [one_div_nonneg]; linarith; assumption

-- Determine when $g$ is positive or negative
    have hg1 : ∀ x, 1 ≤ x → 0 ≤ g x := by
      intro x hx; apply h'g0 at hx
      rw [← show g 1 = 0 by simp [g]]; assumption
      simp; simp; linarith
    have hg2 : ∀ x, (0 < x ∧ x ≤ 1) → g x ≤ 0 := by
      rintro x ⟨hx1, hx2⟩; apply h'g0 at hx2
      rw [← show g 1 = 0 by simp [g]]; assumption
      simp; linarith; simp

-- Prove that $f$ is decreasing when $x$ is between $0$ and $1$
    have hf1 : MonotoneOn (-f) (Set.Ioc 0 1) := by
      apply monotoneOn_of_deriv_nonneg; apply convex_Ioc
      rw [continuousOn_neg_iff, ContinuousOn]
      intro _ h'; simp at h'
      apply ContinuousAt.continuousWithinAt; apply hf0; linarith
      simp; apply DifferentiableOn.neg; intro x hx; simp at hx
      apply DifferentiableAt.differentiableWithinAt
      apply h'f0; linarith
      simp; intro x hx1 hx2
      rw [show -f=(fun y => -f y) by rfl, deriv.neg, derf]; simp
      rw [div_nonpos_iff]; right; constructor
      · apply hg2; constructor; assumption; linarith
      apply pow_two_nonneg; assumption

-- Prove that $f$ is increasing when $x$ is greater or equal to $1$
    have hf2 : MonotoneOn f (Set.Ici 1) := by
      apply monotoneOn_of_deriv_nonneg; apply convex_Ici
      rw [ContinuousOn]; intro x hx; simp at hx
      apply ContinuousAt.continuousWithinAt; apply hf0; linarith
      simp; rw [DifferentiableOn]; intro x hx; simp at hx
      apply DifferentiableAt.differentiableWithinAt
      apply h'f0; linarith
      simp; intro x hx; rw [derf]
      rw [div_nonneg_iff]; left; constructor
      · apply hg1; linarith
      apply pow_two_nonneg; linarith

-- Show that $f$ has a minimum at $x=1$ and prove the final result
    have hf3 : ∀ x, 0 < x → f 1 ≤ f x := by
      intro x hx; by_cases h' : 1 ≤ x
      · rw [MonotoneOn] at hf2
        apply hf2; simp; simp; assumption; assumption
      push_neg at h'; rw [← neg_le_neg_iff]
      rw [MonotoneOn] at hf1; apply hf1
      simp; constructor; linarith; linarith
      simp; linarith
    intro x hx; have := hf3 x hx
    simp [f] at this; assumption
  have := lm1 a ha; linarith; apply exp_pos

/-check that when $a=1$ and $b=1$, the required inequality holds.
Therefore the above minimum can be reached by $a=1$ and $b=1$-/
theorem algebra_9126_2: ∀ x : ℝ, (Real.log 1 + 1) * Real.exp x - 1 ^ 2 * rexp 1 * x ≥ 0 := by
  intro x; simp
  have := Real.add_one_le_exp (x-1)
  simp at this; rw [exp_sub, le_div_iff₀, mul_comm] at this; assumption
  apply exp_pos

/-summarise all the results-/
theorem algebra_9126_3 : IsLeast {t : ℝ | ∃ a b, t = b / a ∧ 0 < a ∧ 
∀ x : ℝ, (Real.log a + b) * Real.exp x - a ^ 2 * rexp 1 * x ≥ 0} 1 := by
  rw [IsLeast]; constructor
  · simp only [Set.mem_setOf_eq]; use 1; use 1
    constructor; norm_num; constructor; norm_num; exact algebra_9126_2
  rw [lowerBounds]; intro y; simp only [Set.mem_setOf_eq]
  rintro ⟨a, b, hy, ha, h⟩; rw [hy]; exact algebra_9126_1 a b ha h