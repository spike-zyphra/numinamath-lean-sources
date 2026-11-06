import Mathlib
open Real Set

/- The number of zeros of the function $f(x)=\begin{cases} |x|-2, & x\leqslant 0, \\ 2x-6+\ln x, & x > 0 \end{cases}$ is ____. -/
theorem algebra_9184 {f : ℝ → ℝ}
  (hf : ∀ x, x ≤ 0 → f x = abs x - 2)
  (hf' : ∀ x, x > 0 → f x = 2 * x - 6 + log x) :
  {x | f x = 0}.ncard = 2 := by

  -- Most important step: prove that there is a unique zero in the interval (0, +∞)
  have ⟨a, ⟨ha, hfa⟩, hau⟩ : ∃! x > 0, f x = 0 := by

    -- Lemma 1: f is continuous on (0, +∞)
    have fcont : ContinuousOn f (Ioi 0) := by
      -- Change f to 2x - 6 + ln x
      refine ContinuousOn.congr ?_ hf'
      -- Apply the lemmas of continuous functions
      apply ContinuousOn.add
      . apply ContinuousOn.sub
        . exact ContinuousOn.mul continuousOn_const continuousOn_id
        . exact continuousOn_const
      . apply ContinuousOn.log continuousOn_id
        -- Need to prove that the expression inside the log is nonzero
        intro x hx
        simp at hx ⊢
        exact ne_of_gt hx

    -- Lemma 2: f is strictly increasing on (0, +∞)
    -- Directly by definition
    have fmono : StrictMonoOn f (Ioi 0) := by
      intro x hx y hy hxy
      rw [hf' x hx, hf' y hy]
      linarith [show log x < log y from log_lt_log hx hxy]

    -- Lemma 3: f is injective on (0, +∞), because it is strictly increasing
    have finj : InjOn f (Ioi 0) := StrictMonoOn.injOn fmono

    -- Lemma 4: f(1) < 0 and f(3) > 0 by calculation
    have h1 : f 1 < 0 := by
      rw [hf' 1 (by norm_num)]
      norm_num

    have h2 : f 3 > 0 := by
      rw [hf' 3 (by norm_num)]
      norm_num
      positivity

    -- (f 1, f 3) is a subset of the image of f on (1, 3) by the intermediate value theorem
    have h3 : Ioo (f 1) (f 3) ⊆ image f (Ioo 1 3) := intermediate_value_Ioo (by norm_num) (ContinuousOn.mono fcont (by intro x hx; simp at hx ⊢; linarith))

    -- Thus 0 is in the image of f on (1, 3)
    -- So there exists x in (1, 3) such that f x = 0
    specialize h3 ⟨h1, h2⟩
    simp at h3
    obtain ⟨a, ha, hfa⟩ := h3

    -- Denote such x as a
    use a
    simp
    -- If f x = 0 = f a, then x = a by injectivity
    refine ⟨⟨by linarith, hfa⟩, fun x hx hfx ↦ ?_⟩
    exact finj hx (show a > 0 by linarith) (show f x = f a by linarith)

  -- It suffices to prove that the set of zeros of f is {-2, a}
  suffices h : {x | f x = 0} = {-2, a} by
    rw [h]
    -- -2 and a are different
    exact ncard_pair (show -2 ≠ a by linarith)

  ext x
  -- Two cases: x ≤ 0 and x > 0
  obtain h | h := le_or_gt x 0
  . -- When x ≤ 0, f x = |x| - 2
    -- f x = 0 iff x = -2
    simp [hf x h, show ¬ x = a by linarith]
    constructor <;> intro hx
    . simp [abs_of_nonpos h] at hx
      linarith
    . subst hx
      norm_num
  . -- When x > 0, f x = 2x - 6 + ln x
    -- f x = 0 iff x = a
    simp [show ¬ x = -2 by linarith]
    constructor <;> intro hx
    . exact hau x ⟨h, hx⟩
    . rwa [hx]
