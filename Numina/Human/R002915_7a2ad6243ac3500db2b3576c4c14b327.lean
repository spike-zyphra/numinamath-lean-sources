import Mathlib

open Real Set

-- Show that the derivative of x^2 - a * x - a is 2 * x - a.
lemma lemma_1 {a x : ℝ} : deriv (fun x => x^2 - a * x - a) x = 2 * x - a := by
  rw [deriv_sub (by fun_prop) (by fun_prop), deriv_sub (by fun_prop) (by fun_prop)]
  rw [deriv_pow, deriv_const_mul _ (by fun_prop)]
  simp

-- Show that if the function x^2 - a * x - a is strictly decreasing on (-∞, b)
-- then 2 * b ≤ a.
lemma lemma_2 {a b : ℝ} (h : StrictAntiOn (fun x => x^2 - a * x - a) (Iio b)) : 2 * b ≤ a := by
  -- Assume that a < 2 * b and show that there exists x < b, y < b such that
  -- x < y and x^2 - a * x - a ≤ y^2 - a * y - a.
  contrapose! h
  simp [StrictAntiOn]
  -- Take x = a / 2 < b and y = (2 * b + a) / 4 < b.
  use a / 2, by linarith
  use (2 * b + a) / 4, by linarith, by linarith
  nlinarith

-- Show that if 2 * b ≤ a then the function x^2 - a * x - a is strictly decreasing on (-∞, b].
lemma lemma_3 {a b : ℝ} (h : 2 * b ≤ a) : StrictAntiOn (fun x => x^2 - a * x - a) (Iic b) := by
  -- It is enough to show that the derivative of x^2 - a * x - a is negative
  -- on (-∞, b].
  apply strictAntiOn_of_deriv_neg (convex_Iic _) (by fun_prop)
  simp only [interior_Iic, mem_Iio]
  intro x hx
  rw [lemma_1]
  linarith

-- Show that if h maps s to t, g is monotone on t,
-- and g ∘ h is strictly decreasing on s, then h is strictly decreasing on s.
lemma lemma_4 {s t : Set ℝ} {g h : ℝ → ℝ}
    (hst : MapsTo h s t) (hg : MonotoneOn g t) (hgh : StrictAntiOn (g ∘ h) s) :
    StrictAntiOn h s := by
  -- Assume that h is not strictly decreasing on s and show that
  -- g ∘ h is not strictly decreasing on s.
  contrapose! hgh
  simp [StrictMonoOn, StrictAntiOn] at hgh ⊢
  -- We can find a ∈ s and b ∈ s such that a < b and h a ≤ h b.
  have ⟨a, ha, b, hb, hab, hgab⟩ := hgh
  use a, ha, b, hb, hab
  -- g (h a) ≤ g (h b) because g is monotone on t and h a ∈ t, h b ∈ t.
  exact hg (hst ha) (hst hb) hgab

-- Show that if 0 < x^2 - a * x - a for all x ∈ (-∞, 1 - √3) then a ≤ 2.
lemma lemma_5 {a : ℝ} (h : ∀ x ∈ Iio (1 - √3), 0 < x^2 - a * x - a) : a ≤ 2 := by
  simp only [mem_Iio] at h
  -- Suppose that 2 < a and show that there exists x ∈ (-∞, 1 - √3) such that
  -- x^2 - a * x - a ≤ 0.
  contrapose! h
  -- Let e = (1 - √3)^2 - a * (1 - √3) - a.
  set e := (1 - √3)^2 - a * (1 - √3) - a with he
  -- We have e < 0.
  have hineq : e < 0 := by
    suffices 2 * (2 - √3) < a * (2 - √3) by
      ring_nf
      simp
      linear_combination this
    gcongr
    rw [sub_pos, show 2 = √(2 ^ 2) by simp]
    apply sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- The function x^2 - a * x - a is continuous.
  have hcont : Continuous (fun x => x^2 - a * x - a) := by fun_prop
  rw [Metric.continuous_iff] at hcont
  have he2 : -e / 2 > 0 := by
    apply div_pos (by linarith) (by linarith)
  -- The continuity of x^2 - a * x - a implies that there exists d > 0
  -- such that |x^2 - a * x - a - e| < -e / 2 for all x such that |x - (1 - √3)| < d.
  have ⟨d, hd, h⟩ := hcont (1 - √3) (-e / 2) he2
  -- Let x = 1 - √3 - d / 2.
  set x := 1 - √3 - d / 2
  -- We have |x - (1 - √3)| < d.
  have hx : |x - (1 - √3)| < d := by simpa [x, abs_div, abs_of_pos hd]
  -- So |x^2 - a * x - a - e| < -e / 2.
  have := h x hx
  use x
  constructor
  -- x < 1 - √3 since d > 0.
  · simp [x]
    linarith
  -- x^2 - a * x - a - e < -e / 2, so x^2 - a * x - a < e / 2 ≤ 0.
  simp [← he, dist, abs_lt] at this
  calc
    x^2 - a * x - a ≤ e / 2 := by linarith
    _ ≤ 0 := by linarith

/- 1. The function $f(x)=-\log _{\frac{1}{2}}\left(x^{2}-a x-a\right)$ is decreasing on the interval $(-\infty, 1-\sqrt{3})$, the range of values for $a$ is $\qquad$ . -/
theorem algebra_129707 {a : ℝ} :
    ((∀ x ∈ Iio (1 - √3), 0 < x^2 - a * x - a) ∧ StrictAntiOn (fun x => -logb (1 / 2) (x^2 - a * x - a)) (Iio (1 - √3))) ↔
    a ∈ Icc (2 * (1 - sqrt 3)) 2 := by
  -- Show that -logb (1 / 2) x = logb 2 x for all x.
  have eq x : -logb (1 / 2) x = logb 2 x := by
    rw [logb_div_base (by norm_num) (by norm_num)]
    simp [inv_neg]
  simp_rw [eq, mem_Icc]
  constructor
  -- Show that 0 < x^2 - a * x - a for all x ∈ (-∞, 1 - √3) and the fact that
  -- logb 2 (x^2 - a * x - a) is strictly decreasing on (-∞, 1 - √3)
  -- imply that a ∈ [2 * (1 - √3), 2].
  · intro ⟨ha, h⟩
    -- Show that x^2 - a * x - a is strictly decreasing on (-∞, 1 - √3).
    have hg : StrictAntiOn (fun x => x^2 - a * x - a) (Iio (1 - √3)) := by
      -- logb 2 is increasing on (0, ∞) so the result follows from lemma 4.
      apply lemma_4 _ (strictMonoOn_logb one_lt_two).monotoneOn h
      intro x hx
      simp only [mem_Ioi]
      apply ha x hx
    -- Lemma 2 implies that 2 * (1 - √3) ≤ a.
    apply lemma_2 at hg
    -- Lemma 5 implies that a ≤ 2.
    apply lemma_5 at ha
    exact ⟨hg, ha⟩
  -- Show that 2 * (1 - √3) ≤ a ≤ 2 implies that
  -- 0 < x^2 - a * x - a for all x ∈ (-∞, 1 - √3) and
  -- logb 2 (x^2 - a * x - a) is strictly decreasing on (-∞, 1 - √3).
  · intro ⟨ha1, ha2⟩
    -- Show that 0 < x^2 - a * x - a for all x ∈ (-∞, 1 - √3).
    have ha : ∀ x ∈ Iio (1 - √3), 0 < x^2 - a * x - a := by
      intro x hx
      -- It is enough to show that 0 ≤ 0 ≤ (1 - √3)^2 - a * (1 - √3) - a.
      suffices 0 ≤ (1 - √3)^2 - a * (1 - √3) - a by
        -- Indeed, lemma 3 implies that (1 - √3)^2 - a * (1 - √3) - a < x^2 - a * x - a
        -- for all x < 1 - √3.
        have h1 := lemma_3 ha1 (mem_Iic_of_Iio hx) right_mem_Iic (by simp_all)
        simp at h1
        linarith
      suffices a * (2 - √3) ≤ 2 * (2 - √3) by
        ring_nf
        simp
        linear_combination this
      gcongr
      rw [sub_nonneg, show 2 = √(2 ^ 2) by simp]
      apply sqrt_le_sqrt (by norm_num)
    refine ⟨ha, ?_⟩
    -- It is left to show that logb 2 (x^2 - a * x - a) is strictly decreasing on (-∞, 1 - √3).
    -- logb 2 is strictly increasing on (0, ∞), so it is enough to show that
    -- x^2 - a * x - a is strictly decreasing on (-∞, 1 - √3).
    -- The result follows from lemma 3.
    apply StrictMonoOn.comp_strictAntiOn (g := logb 2) (strictMonoOn_logb one_lt_two)
    · apply StrictAntiOn.mono (lemma_3 ha1)
      simp only [Iio_subset_Iic_iff, le_refl]
    · intro x hx
      simp only [mem_Ioi]
      apply ha x hx