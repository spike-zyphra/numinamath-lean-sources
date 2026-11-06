import Mathlib

/- For real numbers $x$, let \[f(x) = \left\{
\begin{array}{cl}
x+2 &\text{ if }x>3, \\
2x+a &\text{ if }x\le 3.
\end{array}
\right.\]What must the value of $a$ be to make the piecewise function continuous (which means that its graph can be drawn without lifting your pencil from the paper)? -/
theorem algebra_12869 {a : ℝ} (f : ℝ → ℝ) (hf : ∀ x, x > 3 → f x = x + 2) (hf' : ∀ x, x ≤ 3 → f x = 2 * x + a) :
    Continuous f ↔ a = -1 := by
  apply Iff.intro
  . -- If f is continuous, then a = -1.
    intro f_cont
    -- We only need the continuity at x = 3.
    replace f_cont : ContinuousAt f 3 := by
      apply Continuous.continuousAt
      exact f_cont
    rw [continuousAt_iff_continuous_left_right] at f_cont
    obtain ⟨_, h⟩ := f_cont
    rw [Metric.continuousWithinAt_iff] at h
    by_contra! ha
    rw [ne_iff_lt_or_gt] at ha
    obtain ha | ha := ha
    . -- Suppose a < -1.
      specialize h (-1 - a)
      simp [dist, abs, hf'] at h
      have h' := ha
      apply h at h'
      clear h
      obtain ⟨δ, δpos, h⟩ := h'
      specialize @h (3 + min (-1 - a) (δ / 2))
      have g : -min (-1 - a) (δ / 2) < 0 := by
        nth_rewrite 2 [<-neg_neg 0]
        apply neg_lt_neg
        simp
        refine ⟨?_, ?_⟩
        . linarith only [ha, δpos]
        . linarith only [δpos]
      simp [δpos, show a ≤ -1 by apply le_of_lt ha, show 0 ≤ δ / 2 by linarith only [δpos], show -min (-1 - a) (δ / 2) < δ by linarith only [g, δpos]] at h
      rw [hf] at h
      absurd h
      simp [show 3 + min (-1 - a) (δ / 2) + 2 - (2 * 3 + a) ≥ -1 - a by linarith only [g]]
      linarith only [g]
    . -- Suppose a > -1.
      specialize h ((a + 1) / 2)
      simp [dist, abs, hf'] at h
      replace ha : 0 < a + 1 := by
        linarith only [ha]
      have h' := ha
      replace ha : 0 < (a + 1) / 2 := by
        linarith only [ha]
      apply h at h'
      obtain ⟨δ, δpos, h⟩ := h'
      specialize @h (3 + min ((a + 1) / 2) (δ / 2))
      have g₀ : min ((a + 1) / 2) (δ / 2) > 0 := by
        simp
        refine ⟨?_, ?_⟩
        . linarith only [ha, δpos]
        . linarith only [δpos]
      simp [δpos, show 0 ≤ (a + 1) / 2 by apply le_of_lt ha, show 0 ≤ δ / 2 by linarith only [δpos], show -min ((a + 1) / 2) (δ / 2) < δ by linarith only [g₀, δpos]] at h
      rw [hf] at h
      absurd h
      simp
      intro _
      linarith only [show min ((a + 1) / 2) (δ / 2) ≤ (a + 1) / 2 by simp]
      linarith only [g₀]
  . -- If a = -1, then f is continuous.
    intro ha
    rw [ha] at hf'
    -- f is a piecewise continuous function.
    let f₁ : ℝ → ℝ := fun x => 2 * x + -1
    have f₁_cont : Continuous f₁ := by
      continuity
    have f₁_eq : ∀ x : ℝ, x ≤ 3 → f₁ x = f x := by
      intro x hx
      rw [hf']
      exact hx
    let f₂ : ℝ → ℝ := fun x => x + 2
    have f₂_cont : Continuous f₂ := by
      continuity
    have f₂_eq : ∀ x : ℝ, x ≥ 3 → f₂ x = f x := by
      intro x hx
      by_cases h : x ≤ 3
      . replace h : x = 3 := by
          linarith only [h, hx]
        dsimp [f₂]
        rw [h, hf']
        repeat norm_num
      . simp at h
        dsimp [f₂]
        rw [hf]
        ring_nf
        exact h
    clear a ha hf hf'
    have h : f = (Set.Iic 3).piecewise f₁ f₂ := by
      ext x
      simp only [Set.piecewise]
      split_ifs with h
      . exact symm (f₁_eq x h)
      . simp at h
        exact symm (f₂_eq x (show x ≥ 3 by linarith only [h]))
    rw [h]
    -- By considering the boundaries of {x | x ≤ 3}, f is continuous on the whole ℝ.
    refine Continuous.piecewise ?_ f₁_cont f₂_cont
    simp [f₁, f₂]
    norm_num

