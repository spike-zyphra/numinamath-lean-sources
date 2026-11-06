import Mathlib

open Set

/-Given that the odd function $f(x)$ defined on $\mathbb{R}$ is monotonically increasing on $(0,+\infty)$ and $f(-2)=0$, find the solution set of the inequality $x \cdot f(x) < 0$.-/
theorem algebra_9312 {f : ℝ → ℝ} (hf : ∀ x, f x = - f (-x)) (hinc : StrictMonoOn f (Set.Ioi 0))
    (h2 : f (-2) = 0) :
    {x | x * f x < 0} = Set.Ioo (-2) 0 ∪ Set.Ioo 0 2 := by
      ext x
      simp
      have h2' : f 2 = 0 := by
        rw [hf 2, h2]; simp
      -- we have $f(x) < 0$ when $0 < x < 2$.
      have h1 : ∀ x, 0 < x → x < 2 → f x < 0 := by
        intro x x1 x2
        have : StrictMonoOn f (Ioc 0 2) := by
          rw [←Set.Iic_inter_Ioi]
          exact StrictMonoOn.mono hinc (by simp)
        rw [←h2']
        exact (StrictMonoOn.lt_iff_lt this ⟨x1, le_of_lt x2⟩ (by simp)).2 x2
      -- we have $f(x) > 0$ when $-2 < x < 0$.
      have h1' : ∀ x, -2 < x → x < 0 → 0 < f x := by
        intro y y1 y12
        rw [hf y]
        specialize h1 (-y) (by linarith) (by linarith)
        linarith
      -- we have $0 \leq f(x)$ when $2 \leq x$.
      have h3 : ∀ x, 2 ≤ x → 0 ≤ f x := by
        intro x hx
        rw [←h2']
        exact  (StrictMonoOn.le_iff_le hinc (by simp) (by simp; linarith)).2 hx
      -- Consider $x < 0$ or $x = 0$ or $x > 0$.
      constructor <;> intro h
      · rcases lt_trichotomy x 0 with neg | zero | pos
        · -- if $x < 0$, we have $ f(x) > 0$.
          left
          simp [neg]
          have : 0 < f x := (neg_iff_pos_of_mul_neg h).mp neg
          contrapose! this
          specialize h3 (-x) (by linarith)
          rw [hf x]
          linarith
        · -- there have contradiction when $x = 0$.
          simp [zero] at h
        · -- if $x > 0$, we have $ f(x) < 0$.
          right
          simp [pos]
          have : f x < 0 := (pos_iff_neg_of_mul_neg h).mp pos
          contrapose! this
          exact h3 x this
      · -- Verify that when  $(-2 < x < 0)$ or $(0 < x < 2)$, $x * f(x) < 0$.
        rcases h with neg | pos
        · have hfpos : 0 < f x := h1' x neg.1 neg.2
          refine mul_neg_of_neg_of_pos neg.2 hfpos
        · have hfneg : f x < 0 := h1 x pos.1 pos.2
          refine mul_neg_of_pos_of_neg pos.1 hfneg
