import Mathlib
open Real Set

/- Given the function $f(x)=x^{2}+\frac{a}{x}$, if the function is monotonically increasing for $x\in [2,+\infty)$, then the range of real number $a$ is ____. -/
theorem algebra_9339 {a : ℝ} (f : ℝ → ℝ) (hf : f = λ x => x^2 + a / x) :
  MonotoneOn f (Ici 2) ↔ a ≤ 16 := by

  -- f'(x) = 2x - a/x^2 if x ≠ 0
  have fder x (hx : x ≠ 0) : deriv f x = 2 * x - a / x^2 := by
    -- Use lemmas of differentiation
    rw [hf, deriv_add, deriv_pow, deriv_div] <;> try simp
    . ring
    . exact hx
    . exact DifferentiableAt.div (by simp) (by simp) hx

  -- f is continuous on (0, +∞) by composition of continuous functions
  have fcont : ContinuousOn f (Ioi 0) := by
    rw [hf]
    -- Apply lemmas of continuity
    apply ContinuousOn.add
    . apply ContinuousOn.pow
      exact continuousOn_id
    . apply ContinuousOn.div
      . exact continuousOn_const
      . exact continuousOn_id
      . intro x hx
        simp at hx
        linarith

  -- The derivative of f is continuous on (0, +∞) by composition of continuous functions
  have fdercont : ContinuousOn (fun x => 2 * x - a / x^2) (Ioi 0) := by
    -- Apply lemmas of continuity
    apply ContinuousOn.sub
    . apply ContinuousOn.mul
      . exact continuousOn_const
      . exact continuousOn_id
    . apply ContinuousOn.div
      . exact continuousOn_const
      . apply ContinuousOn.pow
        exact continuousOn_id
      . intro x hx
        simp at hx
        nlinarith

  -- f is differentiable on (0, +∞) by composition of differentiable functions
  have fdiff : DifferentiableOn ℝ f (Ioi 0) := by
    rw [hf]
    -- Apply lemmas of differentiability
    apply DifferentiableOn.add
    . apply DifferentiableOn.pow
      exact differentiableOn_id
    . apply DifferentiableOn.div
      . exact differentiableOn_const a
      . exact differentiableOn_id
      . intro x hx
        simp at hx
        linarith

  -- Split the problem into two goals
  constructor <;> intro h
  . -- If a > 16, then f is not monotonically increasing on [2, +∞)
    by_contra! ha
    -- Set m = f'(2) = 4 - a/4 < 0
    let m := deriv f 2
    have hm : m = 4 - a / 4 := by
      simp [m]
      rw [fder 2 (by norm_num)]
      ring
    have hm1 : m < 0 := by linarith

    -- f' is continuous on (0, +∞), thus there exists δ > 0 such that |f'(x)| < -m for all x in (2-δ, 2+δ)
    -- Use epsilon-delta definition of continuity
    rw [Metric.continuousOn_iff] at fdercont
    obtain ⟨δ, δpos, hδ⟩ := fdercont 2 (by norm_num) (-m) (by linarith)
    simp [dist] at hδ

    -- We prove that f is monotonically decreasing on [2, 2+δ], because f'(x) < 0 for all x in (2, 2+δ)
    have fanti : StrictAntiOn f (Icc 2 (2 + δ)) := by
      -- Apply the lemma of negative derivative implies decreasing function
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)

      . -- We need to prove f is continuous on [2, 2+δ], which is true because f is continuous on (0, +∞)
        apply ContinuousOn.mono fcont
        simp [Icc, Ioi]
        intros
        linarith

      . -- f'(x) < 0 for all x in (2, 2+δ)
        simp
        intro x hx1 hx2
        rw [fder x (by linarith)]
        have hx3 : |x - 2| < δ := by
          rw [abs_lt]
          constructor <;> linarith
        -- Apply x to hδ
        specialize hδ x (by linarith) hx3
        apply lt_of_abs_lt at hδ
        norm_num at hδ
        linarith

    -- f is strictly decreasing on [2, 2+δ], thus f(2+δ) < f(2)
    -- It contradicts the assumption that f is monotonically increasing on [2, +∞)
    simp [MonotoneOn] at h
    specialize @h 2 (by norm_num) (2 + δ) (by linarith) (by linarith)
    simp [StrictAntiOn] at fanti
    specialize @fanti 2 (by norm_num) (by linarith) (2 + δ) (by linarith) (by linarith) (by linarith)
    linarith only [h, fanti]

  . -- If a ≤ 16, then f is monotonically increasing on [2, +∞)

    -- It suffices to prove f'(x) ≥ 0 for all x in (2, +∞)
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)

    . -- We need to prove f is continuous on [2, +∞), which is true because f is continuous on (0, +∞)
      apply ContinuousOn.mono fcont
      simp [Ici, Ioi]
      intros
      linarith

    . -- We need to prove f is differentiable on (2, +∞), which is true because f is differentiable on (0, +∞)
      apply DifferentiableOn.mono fdiff
      simp

    . -- f'(x) ≥ 0 for all x in (2, +∞)
      simp
      intro x hx
      rw [fder x (by linarith)]
      -- f'(x) = 2x - a/x^2
      -- x > 2, 0 < 1/x^2 < 1/4
      -- Thus 2x - a/x^2 > 2*2 - 16/4 = 0
      have hx1 : 1 / x ^ 2 < 1 / 4 := one_div_lt_one_div_of_lt (by norm_num) (by nlinarith)
      have hx2 : 1 / x ^ 2 > 0 := one_div_pos.2 (pow_pos (by nlinarith) 2)
      have ha : a / x ^ 2 = a * (1 / x ^ 2) := by ring
      nlinarith
