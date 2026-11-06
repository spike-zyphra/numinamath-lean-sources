import Mathlib

open Function Monotone

/-Let $\mathbb{R}^{+}$be the set of positive real numbers. Determine all functions $f: \mathbb{R}^{+} \rightarrow \mathbb{R}^{+}$ such that, for all positive real numbers $x$ and $y$,  $$ f(x+f(x y))+y=f(x) f(y)+1 $$-/
theorem algebra_23950 {f : ℝ → ℝ} {fneg : ∀ x, x ≤ 0 → f x = x} (fpos: ∀ x, 0 < x → 0 < f x) :
(∀ x y, 0 < x → 0 < y → f (x + f (x * y)) + y = f x * f y + 1) ↔ ∀ x, 0 < x → f x = x + 1 := by
  constructor; intro hFE
-- Give notations LHS and RHS to the functions on two sides of the functional equation hFE
  let LHS : ℝ → ℝ → ℝ := fun x y => f (x + f (x * y)) + y
  let RHS : ℝ → ℝ → ℝ := fun x y => f x * f y + 1
-- Set $x$ to be $1$ in the functional equation hFE to get the following equality FE1y
  have FE1y := hFE 1; simp at FE1y
-- Prove that $f$ is injective
  have fInj : Injective f := by
    intro a b hab; by_cases h : a ≤ 0
    · have := fneg a h
      suffices : b ≤ 0
      · have := fneg b this; linarith
      by_contra h'; push_neg at h'
      have := fpos b h'; linarith
    push_neg at h; have fapos := fpos a h
    by_cases h' : b ≤ 0
    · have := fneg b h'; linarith
    push_neg at h'; have fbpos := fpos b h'
    have aux_b := FE1y b h'; have aux_a := FE1y a h
    apply_fun (fun t => t - f (1 + f b)) at aux_b; ring_nf at aux_b
    apply_fun (fun t => t - f (1 + f a)) at aux_a; ring_nf at aux_a
    rw [hab, ← aux_b] at aux_a; assumption
-- Prove that $f$ is strictly increasing by contradiction, we will construct two numbers $x1$ and $x2$ violating the injectivity of $f$
  have fStricMono : StrictMono f := by
    rw [StrictMono]; by_contra h; push_neg at h
    rcases h with ⟨a, b, ⟨altb, fbgtfa⟩⟩
    replace fbgtfa : f b < f a := by
      by_contra; suffices : f b = f a
      apply fInj at this; any_goals linarith
    by_cases bpos : b ≤ 0
    · repeat rw [fneg] at fbgtfa
      any_goals linarith
    push_neg at bpos; have fbpos := fpos b bpos; by_cases apos : a ≤ 0
    · nth_rw 2 [fneg] at fbgtfa; any_goals linarith
    push_neg at apos; have fapos := fpos a apos
    set y := (b - a) / (f a - f b) with hy
    have ypos : 0 < y := by rw [hy]; apply div_pos; any_goals linarith
    have fypos : 0 < f y := fpos y ypos
    set x1 := a / y with hx1; set x2 := b / y with hx2
    have xpos : 0 < x1 ∧ 0 < x2 := by
      rw [hx1, hx2]; constructor; any_goals apply div_pos; any_goals linarith
    suffices : f (x1 + f (x1 * y)) = f (x2 + f (x2 * y))
    · apply_fun (fun t => t + y) at this; repeat rw [hFE] at this
      simp at this; cases this; any_goals linarith
      rename_i h; apply fInj at h; rw [hx1, hx2] at h
      field_simp at h; linarith
    apply fInj; rw [hx1, hx2, hy]
    have : 0 < b - a := by linarith
    have : 0 < f a - f b := by linarith
    field_simp; ring_nf
-- According to the reference answer, we define the following quantities $p$, $q$ via right limits of $f$
  set p := rightLim f 0 with pprop; let q := rightLim f p 
-- Prove the following property of the right limit $p$, the mathlib results we mainly use here are
-- tendsto_rightLim_within and Metric.tendsto_nhdsWithin_nhdsWithin
  have hp : ∀ b, p < b → ∃ i, 0 < i ∧ ∀ a, 0 < a ∧ a < i → f a < b := by
    intro b hb;
    have := tendsto_rightLim_within (show Monotone f by exact StrictMono.monotone fStricMono) 0
    simp [Metric.tendsto_nhdsWithin_nhdsWithin] at this
    rcases this (b-p) (show _ by linarith) with ⟨w, ⟨wpos,hw⟩⟩
    use w; constructor; assumption
    intro a ha; rcases @hw a ha.left (show _ by rw [abs_eq_self.mpr]; any_goals linarith) with ⟨_,tmph1⟩
    rw [dist_eq_norm_sub, Real.norm_eq_abs, abs_eq_self.mpr, ← pprop] at tmph1
    simp at tmph1; assumption; linarith
-- Prove the following key fact that comes from the reference answer, the key fact implies $f$ is linear for all positive real numbers
  have key : ∀ y, 0 < y → q + y = p * f y + 1 := by
    intro y hy; have fypos : 0 < f y := fpos y hy
  -- Fixing the second variable of LHS, denote the function in $x$ by $l$
    let l : ℝ → ℝ := fun x => LHS x y
  -- Fixing the second variable of RHS, denote the function in $x$ by $r$
    let r : ℝ → ℝ := fun x => RHS x y
  -- Prove $l$ is monotone by applying various operations and properties of monotone functions
    have lmono : Monotone l := by
      simp only [l, LHS]; apply add_const; apply Monotone.comp;
      exact StrictMono.monotone fStricMono
      apply Monotone.add; exact fun ⦃a b⦄ a => a; apply Monotone.comp
      exact StrictMono.monotone fStricMono; apply mul_const
      exact fun ⦃a b⦄ a => a; linarith
  -- Prove $r$ is monotone by applying various operations and properties of monotone functions
    have rmono : Monotone r := by
      simp only [r, RHS]; apply add_const; apply mul_const;
      exact StrictMono.monotone fStricMono; linarith
  -- Prove that taking right limit of l and r at $0$ results in a same value
    have lrLim: rightLim l 0 = rightLim r 0 := by
      simp only [l, r, LHS, RHS]; rw [rightLim_eq_sInf, rightLim_eq_sInf]
      rw [sInf_image', sInf_image', iInf_congr]
      intro x; apply hFE; exact x.prop; any_goals assumption
      any_goals exact Filter.NeBot.ne'
  -- Use rightLim_eq_sInf and sInf_image' to rewrite the right limits as iInf
    simp [l, r, LHS, RHS] at lrLim
    rw [rightLim_eq_sInf, rightLim_eq_sInf] at lrLim
    rw [sInf_image', sInf_image', ← ciInf_add, ← ciInf_add] at lrLim
    rw [← Real.iInf_mul_of_nonneg] at lrLim
  -- Assume the following equality of the right limit $q$ and an iInf, we can prove the goal
    suffices : q = ⨅ i : Set.Ioi 0, f (i.val + f (i.val * y))
    · rw [← this, ← sInf_image', ← rightLim_eq_sInf] at lrLim
      assumption; exact StrictMono.monotone fStricMono
      exact Filter.NeBot.ne'
  -- To prove the above equality, we need some preparation.
  -- First we rewrite the right limit $q$ as an iInf by applying rightLim_eq_sInf, sInf_image'
    simp only [q]; rw [rightLim_eq_sInf, sInf_image']
  -- Prove the following auxillary lemma about the right limit $q$ for later use
    have aux_p : ∀ x, 0 < x → p < x + f (x * y) := by
      intro x hx; simp only [p]; rw [rightLim_eq_sInf, sInf_image', ciInf_lt_iff]
      use ⟨x * y, show _ by simp; apply mul_pos; any_goals assumption⟩; linarith
      use 0; simp [lowerBounds]; intros; apply le_of_lt
      apply fpos; assumption; exact StrictMono.monotone fStricMono
      exact Filter.NeBot.ne'
  -- Define a substitution function $g$ between Set.Ioi 0 and Set.Ioi p via aux_p
    set g : Set.Ioi 0 → Set.Ioi p := fun t => ⟨t.val + f (t.val * y), show _ by simp; apply aux_p; exact t.property⟩ with hg
  -- Rewrite the RHS of the goal in terms of the substitution function $g$
    have tmph1 : ∀ i : Set.Ioi (0:ℝ), f ((i.val) + f (i.val * y)) = (Set.Ioi (p:ℝ)).restrict f (g i) := by
      intro i; rw [Set.restrict_apply]
  -- Prove $g$ has a limit at bottom filters
    have tmph2 : Filter.Tendsto g Filter.atBot Filter.atBot := by
      rw [Filter.tendsto_atBot_atBot]; intro b; simp
      obtain ⟨w, ⟨wpos, hw⟩⟩ := hp (p + (b.val - p ) / 2) (show _ by simp; apply b.prop)
      use (b.val - p) / 2 ⊓ w / (2 * y); constructor
      · simp; constructor; apply b.prop
        apply div_pos; assumption
        simp; assumption
      intro a apos ha; simp at ha
      simp [g]; rw [Subtype.mk_le_mk]
      suffices : f (a * y) < p + (b.val - p) / 2; linarith
      apply hw; constructor
      · apply mul_pos; any_goals assumption
      rw [← lt_div_iff]; suffices : w / (2 * y) < w / y; linarith
      rw [div_lt_div_iff]; ring_nf; rw [lt_mul_iff_one_lt_right]; norm_num
      apply mul_pos; any_goals assumption
      simp; assumption
  -- Apply ciInf_comp_tendsto_atBot_of_linearOrder to finish the main goal
    rw [← iInf_congr (Set.restrict_apply f (Set.Ioi p)), iInf_congr tmph1]
    rw [ciInf_comp_tendsto_atBot_of_linearOrder (show _ by apply Monotone.restrict; exact StrictMono.monotone fStricMono) tmph2]
  -- Finish the rest trivial goals
    exact StrictMono.monotone fStricMono; any_goals exact Filter.NeBot.ne'
    linarith
    any_goals assumption
    · use 0; rw [lowerBounds]; simp; intros; rw [mul_nonneg_iff_right_nonneg_of_pos]
      linarith; apply fpos; assumption
    · use 0; rw [lowerBounds]; simp; intros; apply le_of_lt
      apply fpos; apply add_pos; assumption
      apply fpos; apply mul_pos; any_goals assumption
-- Prove that $p$ is positive
  have ppos : 0 < p := by
    rw [lt_iff_le_and_ne]; constructor
    · simp only [p]; rw [Monotone.rightLim_eq_sInf, sInf_image']
      apply le_ciInf; simp; intros; apply le_of_lt
      apply fpos; assumption; exact StrictMono.monotone fStricMono
      exact Filter.NeBot.ne'
    intro h; simp [← h] at key
    have := key 1; simp at this
    have := key 2; simp at this; linarith
-- Rearrange the terms and coefficients in the key lemma
  obtain ⟨a, b, fLin⟩ : ∃ a b , ∀ x, 0 < x → f x = a * x + b := by
    use 1/p; use (q-1)/p; intro x hx; field_simp; ring_nf
    have := key x hx; apply_fun (fun t => t - 1) at this
    ring_nf at this; rw [mul_comm, ← this]; ring
-- Plug in the linear expression fLin to the functional equation hFE and simplify
  have tmph1 : ∀ x y, 0 < x → 0 < y → (a - a * b) * x + (1 - a * b) * y = - a * b - b + b ^ 2 + 1 := by
    intro x y xpos ypos; ring_nf
    have aux := hFE x y xpos ypos
    have hx := fLin x xpos; have hy := fLin y ypos
    have hcomp := fLin (x+f (x*y)) (show _ by apply add_pos; assumption; apply fpos; apply mul_pos; any_goals assumption)
    have hxy := fLin (x * y) (show _ by apply mul_pos; any_goals assumption)
    rw [hx, hy, hcomp, hxy] at aux
    apply_fun (fun t => t - a * b - a ^ 2 * x * y - b - a * x * b - a * b * y) at aux
    ring_nf at aux; rw [← aux]; ring
-- Plug in some special values for $x$ and $y$ to get equations about $a$ and $b$, then solve for $a$ and $b$
  have tmph2 := tmph1 1 1; simp at tmph2
  have tmph3 := tmph1 2 1; simp at tmph3
  have tmph4 := tmph1 1 2; simp at tmph4
  rw [← tmph2, ← sub_eq_zero] at tmph3; ring_nf at tmph3
  rw [← tmph2, ← sub_eq_zero] at tmph4; ring_nf at tmph4
  rw [← tmph3] at tmph4; simp at tmph4
  rw [← tmph4, one_mul, sub_eq_zero] at tmph3
  simp [← tmph3, ← tmph4] at fLin; assumption
-- Conversely, it is straightfoward to check that $f(x)=x+1$ satisfies the functional equation in question
  intro h x y xpos ypos
  repeat rw [h]
  ring; any_goals assumption
  · apply mul_pos; any_goals assumption
  apply add_pos; assumption; apply fpos
  apply mul_pos; any_goals assumption
