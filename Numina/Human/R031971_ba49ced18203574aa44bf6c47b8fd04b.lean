import Mathlib

/- Let \[f(x) =
\begin{cases}
2x^2 - 3&\text{if } x\le 2, \\
ax + 4 &\text{if } x>2.
\end{cases}
\]Find $a$ if the graph of $y=f(x)$ is continuous (which means the graph can be drawn without lifting your pencil from the paper). -/
theorem algebra_10189 {f : ℝ → ℝ} (hf : ∀ x, x ≤ 2 → f x = 2 * x ^ 2 - 3) (hf' : ∀ x, x > 2 → f x = a * x + 4) :
    Continuous f ↔ a = 1 / 2 := by
  apply Iff.intro
  . -- If f is continuous, then a = 1 / 2.
    intro f_cont
    -- We only need the continuity at a = 1 / 2.
    replace f_cont : ContinuousAt f 2 := by
      apply Continuous.continuousAt
      exact f_cont
    rw [continuousAt_iff_continuous_left_right] at f_cont
    obtain ⟨_, h⟩ := f_cont
    rw [Metric.continuousWithinAt_iff] at h
    by_contra! ha
    rw [ne_iff_lt_or_gt] at ha
    obtain ha | ha := ha
    . -- Suppose a < 1 / 2.
      by_cases ha' : a ≤ 0
      . -- If a ≤ 0, contradiction.
        specialize h (1 / 2)
        simp [dist, abs, hf, -one_div] at h
        obtain ⟨δ, δpos, h⟩ := h
        replace h : 2 ≤ (2 + δ / 2) → (2 + δ / 2) - 2 < δ → 2 - (2 + δ / 2) < δ → f (2 + δ / 2) - (2 * 2 ^ 2 - 3) < 1 / 2 ∧ 2 * 2 ^ 2 - 3 - f (2 + δ / 2) < 1 / 2 := by
          apply h
        simp [δpos, show 0 ≤ δ / 2 by linarith only [δpos], show -(δ / 2) < δ by linarith only [δpos], -one_div] at h
        rw [hf'] at h
        nlinarith only [ha, ha', h, δpos]
        linarith only [δpos]
      . -- If 0 < a < 1 / 2, contradiction.
        specialize h (1 / 2 - a)
        simp [show 1 / 2 - a > 0 by linarith only [ha], dist, abs, -one_div, hf] at h
        norm_num at h
        obtain ⟨δ, δpos, h⟩ := h
        let x : ℝ := (1 - 2 * a) * (δ / (1 + δ)) + 2
        have hx₀ : x > 2 := by
          dsimp [x]
          simp [-one_div]
          apply mul_pos
          linarith only [ha]
          rw [div_eq_mul_inv]
          apply mul_pos
          exact δpos
          rw [inv_pos]
          linarith only [δpos]
        have hx₁ : δ / (1 + δ) < 1 := by
          calc
            δ / (1 + δ) < (1 + δ) / (1 + δ) := by apply div_lt_div_of_pos_right; repeat linarith only [δpos]
            _ = 1 := by field_simp
        have hx₂ : x - 2 < 1 / (2 * a) - 1 := by
          calc
            x - 2 = (1 - 2 * a) * (δ / (1 + δ)) := by dsimp [x]; ring
            _ < (1 - 2 * a) / 1 := by rw [div_one]; nth_rewrite 2 [<-mul_one (1 - 2 * a)]; apply mul_lt_mul_of_pos_left; exact hx₁; linarith only [ha]
            _ < (1 - 2 * a) / (2 * a) := by apply div_lt_div_of_pos_left; linarith only [ha]; linarith only [ha']; linarith only [ha]
            _ = 1 / (2 * a) - 1 := by ring_nf; rw [mul_inv_cancel₀]; linarith only [ha']
        replace hx₂ : x - 1 < 1 / (2 * a) := by
          calc
            x - 1 = x - 2 + 1 := by ring
            _ < 1 / (2 * a) - 1 + 1 := by linarith only [hx₂]
            _ = 1 / (2 * a) := by ring
        have hx₃ : x - 2 < δ := by
          calc
            x - 2 = (1 - 2 * a) * (δ / (1 + δ)) := by dsimp [x]; ring
            _ < 1 * (δ / (1 + δ)) := by apply mul_lt_mul_of_pos_right; linarith only [ha']; rw [div_eq_mul_inv]; apply mul_pos; exact δpos; rw [inv_pos]; linarith only [δpos]
            _ < δ / 1 := by rw [one_mul]; apply div_lt_div_of_pos_left; exact δpos; norm_num; linarith only [δpos]
            _ = δ := by rw [div_one]
        specialize @h x
        simp [show x ≥ 2 by linarith only [hx₀], hx₃, show 2 - x < δ by linarith only [δpos, hx₀], hf' x hx₀, -one_div] at h
        obtain ⟨_, h₁⟩ := h
        rw [show 5 - (a * x + 4) = 1 - a * x by ring_nf] at h₁
        absurd h₁
        simp [-one_div]
        rw [neg_le_neg_iff.symm]
        suffices _ : a * (x - 1) < 1 / 2 by
          linarith
        calc
          a * (x - 1) < a * (1 / (2 * a)) := by apply mul_lt_mul_of_pos_left; exact hx₂; linarith only [ha']
          _ = 1 / 2 := by ring_nf; rw [mul_inv_cancel₀]; norm_num; linarith only [ha']
    . -- Suppose a > 1 / 2.
      specialize h (a - 1 / 2)
      simp [show 0 < a - 1 / 2 by linarith only [ha], dist, abs, -one_div, hf] at h
      norm_num at h
      obtain ⟨δ, δpos, h⟩ := h
      specialize @h (2 + δ / 2)
      simp [show 2 ≤ 2 + δ / 2 by linarith only [δpos], δpos, show -(δ / 2) < δ by linarith only [δpos], hf', -one_div] at h
      obtain ⟨h₀, _⟩ := h
      nlinarith only [ha, δpos, h₀]
  . -- If a = 1 / 2, then f is continuous.
    intro ha
    rw [ha] at hf'
    -- f is a piecewise continuous function.
    let f₁ : ℝ → ℝ := fun x => 2 * x ^ 2 - 3
    have f₁_cont : Continuous f₁ := by
      continuity
    have f₁_eq : ∀ x : ℝ, x ≤ 2 → f₁ x = f x := by
      intro x hx
      rw [hf]
      exact hx
    let f₂ : ℝ → ℝ := fun x => x / 2 + 4
    have f₂_cont : Continuous f₂ := by
      continuity
    have f₂_eq : ∀ x : ℝ, x ≥ 2 → f₂ x = f x := by
      intro x hx
      by_cases h : x ≤ 2
      . replace h : x = 2 := by
          linarith only [h, hx]
        dsimp [f₂]
        rw [h, hf]
        repeat norm_num
      . simp at h
        dsimp [f₂]
        rw [hf']
        ring_nf
        exact h
    clear a ha hf hf'
    have h : f = (Set.Iic 2).piecewise f₁ f₂ := by
      ext x
      simp only [Set.piecewise]
      split_ifs with h
      . exact symm (f₁_eq x h)
      . simp at h
        exact symm (f₂_eq x (show x ≥ 2 by linarith only [h]))
    rw [h]
    -- By considering the boundaries of {x | x ≤ 2}, f is continuous on the whole ℝ.
    refine Continuous.piecewise ?_ f₁_cont f₂_cont
    simp [f₁, f₂]
    norm_num
