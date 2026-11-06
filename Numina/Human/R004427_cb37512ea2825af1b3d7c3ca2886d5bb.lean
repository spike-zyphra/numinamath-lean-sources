import Mathlib

open Real Set

-- Show that if h is surjective from s to t, h is strictly monotone on s,
-- and g ∘ h is strictly monotone on s, then g is strictly monotone on t.
lemma lemma_1 {s t : Set ℝ} {g h : ℝ → ℝ}
    (hst : Set.SurjOn h s t) (hh : StrictMonoOn h s) (hgh : StrictMonoOn (g ∘ h) s) :
    StrictMonoOn g t := by
  -- Assume that g is not strictly monotone on t and show that
  -- g ∘ h is not strictly monotone on s.
  contrapose! hgh
  simp [StrictMonoOn] at hgh ⊢
  -- We can find a ∈ t and b ∈ t such that a < b and g b ≤ g a.
  have ⟨a, ha, b, hb, hab, hgab⟩ := hgh
  -- Surjectivity of h implies that for any y ∈ t
  -- there exists x ∈ s such that h x = y.
  have hs {y} (hy : y ∈ t) : ∃ x ∈ s, h x = y := by
    apply Set.mem_of_subset_of_mem hst hy
  -- We can find x1 ∈ s such that h x1 = a.
  have ⟨x1, hx1, hax1⟩ := hs ha
  -- We can find x2 ∈ s such that h x2 = b.
  have ⟨x2, hx2, hbx2⟩ := hs hb
  -- Show that x1 < x2 and g(h x2) ≤ g(h x1).
  use x1, hx1, x2, hx2
  -- We have g(h x2) = g b ≤ g a = g(h x1).
  simp [hax1, hbx2, hgab]
  -- h is strictly monotone on s, so a = h x1 < h x2 = b implies
  -- that x1 < x2.
  rwa [← hh.lt_iff_lt hx1 hx2, hax1, hbx2]

-- Show that if h is surjective from s to t, h is strictly decreasing on s,
-- and g ∘ h is strictly monotone on s, then g is strictly decreasing on t.
lemma lemma_2 {s t : Set ℝ} {g h : ℝ → ℝ}
    (hst : Set.SurjOn h s t) (hh : StrictAntiOn h s) (hgh : StrictMonoOn (g ∘ h) s) :
    StrictAntiOn g t := by
  -- Assume that g is not strictly decreasing on t and show that
  -- g ∘ h is not strictly monotone on s.
  contrapose! hgh
  simp [StrictMonoOn, StrictAntiOn] at hgh ⊢
  -- We can find a ∈ t and b ∈ t such that a < b and g a ≤ g b.
  have ⟨a, ha, b, hb, hab, hgab⟩ := hgh
  -- Surjectivity of h implies that for any y ∈ t
  -- there exists x ∈ s such that h x = y.
  have hs {y} (hy : y ∈ t) : ∃ x ∈ s, h x = y := by
    apply Set.mem_of_subset_of_mem hst hy
  -- We can find x1 ∈ s such that h x1 = a.
  have ⟨x1, hx1, hax1⟩ := hs ha
  -- We can find x2 ∈ s such that h x2 = b.
  have ⟨x2, hx2, hbx2⟩ := hs hb
  -- Show that x2 < x1 and g(h x1) ≤ g(h x2).
  use x2, hx2, x1, hx1
  -- We have g(h x1) = g a ≤ g b = g(h x2).
  simp [hax1, hbx2, hgab]
  -- h is strictly decreasing on s, so a = h x1 < h x2 = b implies
  -- that x2 < x1.
  rwa [← hh.lt_iff_lt hx1 hx2, hax1, hbx2]

-- Assume that 0 < a and a ≠ 1.
-- Show that the function t * (t - (3 * a ^ 2 + 1))
-- is strictly decreasing on (0, 1] iff √3 / 3 ≤ a.
lemma lemma_3 {a : ℝ} (ha : 0 < a ∧ a ≠ 1) : StrictAntiOn (fun t => t * (t - (3 * a ^ 2 + 1))) (Ioc 0 1) ↔ √3 / 3 ≤ a := by
  -- Define c = 3 * a ^ 2 + 1.
  set c := 3 * a ^ 2 + 1
  -- We have 2 ≤ c ↔ √3 / 3 ≤ a.
  have hineq : 2 ≤ c ↔ √3 / 3 ≤ a := calc
    2 ≤ c ↔ 1 / 3 ≤ a ^ 2 := by
      dsimp [c]
      constructor <;> (intros; linarith)
    _ ↔ √(1 / 3) ^ 2 ≤ a ^ 2 := by
      rw [sq_sqrt (by norm_num)]
    _ ↔ √(1 / 3) ≤ a := by
      rw [sq_le_sq₀ (by positivity) (by linarith)]
    _ ↔ √3 / 3 ≤ a := by
      suffices √(1 / 3) = √3 / 3 by rw [this]
      field_simp
  constructor
  -- Show that if g(t) = t * (t - (3 * a ^ 2 + 1)) is strictly decreasing on (0, 1],
  -- then √3 / 3 ≤ a.
  · intro hg
    -- Suppose that a < √3 / 3 and show that g(t) is not
    -- strictly decreasing on (0, 1].
    contrapose! hg
    -- √3 / 3 ≤ a implies that c < 2.
    replace hineq : c < 2 := by
      contrapose! hg
      rwa [← hineq]
    simp [StrictAntiOn]
    -- Show that 0 < c / 2 < 1 and g(c / 2) ≤ g(1).
    use c / 2, by positivity, by linear_combination (le_of_lt hineq) / 2
    use 1, zero_lt_one, le_refl _, by linear_combination hineq / 2
    -- We have g(t) = (t - c / 2)^2 - (c / 2)^2, so
    -- g(c / 2) = -(c / 2)^2 and g(1) = (1 - c / 2)^2 - (c / 2)^2 ≥ -(c / 2)^2.
    simp_rw [show ∀ t, t * (t - c) = (t - c / 2)^2 - (c / 2)^2 by intros; ring]
    nlinarith
  -- Show that √3 / 3 ≤ a implies that g(t) is strictly decreasing on (0, 1].
  · intro h
    -- Show that the derivative of g(t) is negative in (0, 1).
    apply strictAntiOn_of_deriv_neg (convex_Ioc _ _) (by fun_prop)
    simp only [interior_Ioc, mem_Ioo, and_imp]
    intro x hx1 hx2
    rw [deriv_mul (by fun_prop) (by fun_prop), deriv_sub (by fun_prop) (by fun_prop),
        deriv_const, deriv_id'']
    simp
    -- The derivative of g(t) is 2 * x - c.
    -- It is enough to show that 2 ≤ c which is equivalent to √3 / 3 ≤ a.
    suffices 2 ≤ c by linarith
    exact hineq.mpr h

/- (2) If the function $f(x)=a^{x}\left(a^{x}-3 a^{2}-1\right)(a>0$ and $a \neq 1)$ is increasing on the interval $[0,+\infty)$, then the range of the real number $a$ is ( ).
(A) $\left(0, \frac{2}{3}\right]$
(B) $\left[\frac{\sqrt{3}}{3}, 1\right)$
(C) $(0, \sqrt{3}]$
(D) $\left[\frac{3}{2},+\infty\right)$ -/
theorem algebra_265178 {a : ℝ} (ha : 0 < a ∧ a ≠ 1)
    (f : ℝ → ℝ) (hf : f = λ x => a^x * (a^x - 3 * a^2 - 1)) :
    StrictMonoOn f (Ici 0) ↔ √3 / 3 ≤ a ∧ a < 1 := by
  -- Define g(t) = t * (t - (3 * a ^ 2 + 1)).
  set g : ℝ → ℝ := fun t => t * (t - (3 * a ^ 2 + 1))
  -- We have f = g ∘ (a ^ ·).
  have hfg : f = g ∘ (a ^ ·) := by ext x; simp [hf]; ring
  -- We proved that g is strictly decreasing on (0, 1] iff √3 / 3 ≤ a.
  have hg := lemma_3 ha
  constructor
  -- Show that if f is strictly monotone on [0, ∞) then √3 / 3 ≤ a < 1.
  · intro hf
    rw [hfg] at hf
    -- Consider two cases: a < 1 and 1 ≤ a.
    by_cases ha1 : a < 1
    · refine ⟨?_, ha1⟩
      -- If a < 1 then it is enough to show that g is strictly decreasing on (0, 1].
      rw [← hg]
      -- We know that f = g ∘ (a ^ ·) is strictly monotone on [0, ∞).
      -- Apply lemma_2 to g and a ^ x.
      apply lemma_2 (h := fun x => a ^ x) (s := Set.Ici 0) _ _ hf
      -- Show that a ^ x is surjective from [0, ∞) to (0, 1].
      · intro x
        simp only [mem_Ioc, mem_image, mem_Ici, and_imp]
        intro hx1 hx2
        -- It is enough to show that 0 ≤ logb a x for x ∈ (0, 1] and a ^ logb a x = x.
        use logb a x
        simp [rpow_logb ha.1 ha.2 hx1]
        apply logb_nonneg_of_base_lt_one ha.1 ha1 hx1 hx2
      -- Show that a ^ x is strictly decreasing on [0, ∞).
      · apply StrictAnti.strictAntiOn
        apply strictAnti_rpow_of_base_lt_one ha.1 ha1
    -- Suppose now that 1 ≤ a.
    -- a ≠ 1 implies that 1 < a.
    · replace ha1 : 1 < a := by
        rw [lt_iff_le_and_ne]
        simp at ha1
        exact ⟨ha1, ha.2.symm⟩
      -- Show that a ^ x is surjective from [0, ∞) to [1, ∞).
      have hsurj : SurjOn (fun x : ℝ => a ^ x) (Ici 0) (Ici 1) := by
        intro x
        simp only [mem_Ici, mem_image]
        intro hx
        -- It is enough to show that 0 ≤ logb a x and a ^ logb a x = x.
        use logb a x
        simp [rpow_logb ha.1 ha.2 (by linarith)]
        exact logb_nonneg ha1 hx
      -- Show that a ^ x is strictly monotone on [0, ∞).
      have hmono : StrictMonoOn (fun x : ℝ => a ^ x) (Ici 0) := by
        apply StrictMono.strictMonoOn
        apply strictMono_rpow_of_base_gt_one ha1
      -- We know that f = g ∘ (a ^ ·) is strictly monotone on [0, ∞).
      -- Apply lemma_2 to g and a ^ x and get that g is strictly monotone
      -- on [1, ∞).
      have := lemma_1 hsurj hmono hf
      -- Derive a contradiction: show that g((3 * a ^ 2 + 1) / 2) ≤ g(1) and
      -- 1 < (3 * a ^ 2 + 1) / 2.
      contrapose! this
      simp [StrictMonoOn]
      use 1, le_refl _, (3 * a ^ 2 + 1) / 2, by nlinarith, by nlinarith
      have hg_eq t : g t = (t - (3 * a ^ 2 + 1) / 2) ^ 2 - ((3 * a ^ 2 + 1) / 2)^2 := by ring
      simp_rw [hg_eq]
      nlinarith [g]
  -- Assume that √3 / 3 ≤ a < 1 and show that f is strictly monotone on [0, ∞).
  · intro ⟨ha1, ha2⟩
    rw [hfg]
    -- It is enough to show that g is strictly decreasing on (0, 1],
    -- a ^ x is strictly decreasing on [0, ∞), and
    -- a ^ x maps [0, ∞) to (0, 1].
    apply StrictAntiOn.comp (t := Ioc 0 1)
    · exact hg.mpr ha1
    · apply StrictAnti.strictAntiOn
      apply strictAnti_rpow_of_base_lt_one ha.1 ha2
    · simp only [MapsTo, mem_Ici, mem_Ioc]
      intro x hx0
      refine ⟨rpow_pos_of_pos ha.1 _, ?_⟩
      apply rpow_le_one <;> linarith