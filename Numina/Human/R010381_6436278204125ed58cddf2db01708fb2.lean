import Mathlib

open Real Set
open scoped BigOperators

/-Given $a{e}^{ax}-ln(x+\frac{2}{a})-2≥0$ always holds for $(-\frac{2}{a},+∞)$, the range of real number $a$ is ____.-/
theorem algebra_9297 {a : ℝ} (ha : a ≠ 0) :
    (∀ x > -2 / a, a * exp (a * x) - log (x + 2 / a) - 2 ≥ 0) ↔
    a ≥ exp 1 := by
  -- before getting down to business we define and prove certain properties of some functions used in the problem.
  let func := fun x => a * rexp x - x - 2
  let f := fun x => x + log x
  -- find the derivative of $f$
  have dev : ∀ x ∈ (Set.Ioi 0), deriv f x = 1 + 1 / x := by
    unfold_let f
    intro x h; rw [deriv_add]; simp only [deriv_id'', deriv_log', one_div]
    exact differentiableAt_id'
    refine differentiableAt_log ?h.hg.hx
    exact Ne.symm (ne_of_lt h)
  -- find the derivative of $func$
  have funcde: ∀ x : ℝ, deriv func x = a * rexp x - 1 := by
    intro x
    rw [deriv_sub, deriv_sub]; simp only [deriv_id'', deriv_div_const, deriv_const', zero_div,
      sub_zero, sub_left_inj]
    rw [deriv_mul]; simp only [deriv_const', zero_mul, Real.deriv_exp, zero_add]
    simp only [differentiableAt_const]
    exact differentiableAt_exp
    refine DifferentiableAt.const_mul ?hf.ha a
    exact differentiableAt_exp
    exact differentiableAt_id'
    refine (DifferentiableAt.sub_iff_right ?hk.hg).mpr ?hf.a
    refine DifferentiableAt.const_mul ?hk.hg.ha a
    exact differentiableAt_exp
    exact differentiableAt_id'
    exact differentiableAt_const 2
  -- prove that $f$ is strictly monotone on $(0,\infty)$
  have mono : StrictMonoOn f (Set.Ioi 0) := by
    refine strictMonoOn_of_deriv_pos ?hD ?hp ?hf'
    exact convex_Ioi 0
    refine ContinuousOn.add ?hf.hf ?hf.hg
    exact continuousOn_id' (Set.Ioi 0)
    refine ContinuousAt.continuousOn ?hf.hg.hcont
    intro x h; simp only [continuousAt_log_iff, ne_eq]
    by_contra yp; rw [yp] at h; simp only [mem_Ioi, lt_self_iff_false] at h
    intro x h
    have pos : x > 0 := by
      unfold interior at h
      simp only [gt_iff_lt, mem_sUnion, mem_setOf_eq] at h
      rcases h with ⟨t, ⟨⟨_, h₁₂⟩, h₂⟩⟩
      have : x ∈ (Set.Ioi 0) := h₁₂ h₂
      simp only [mem_setOf_eq] at this
      exact h₁₂ h₂
    have : deriv f x = 1  + 1 / x := dev x pos
    rw [this]
    have : 1 / x > 0 :=  one_div_pos.mpr pos
    linarith
  -- we divide the problem into twp parts: get the desired answer and checking it is valid
  constructor
  intro h
  -- if $a<0$ take $x=-\frac2a+1$ to find contradiction.
  by_cases hyp : a < 0
  absurd h; simp only [gt_iff_lt, ge_iff_le, sub_nonneg, not_forall, Classical.not_imp, not_le]
  use -2 / a + 1
  simp only [lt_add_iff_pos_right, zero_lt_one, exists_const]
  have : rexp (a * (-2 / a + 1)) > 0 := exp_pos (a * (-2 / a + 1))
  have : -2 / a + 1 + 2 / a = 1 := by ring
  rw [this]; simp only [log_one, sub_zero, gt_iff_lt]; nlinarith
  -- we notice that the given inequality can be written in nicer form and with monotone property of $f$ we can simplify the problem
  push_neg at hyp; have p : a > 0 := lt_of_le_of_ne hyp (id (Ne.symm ha))
  have g : ∀ x > -2 / a, a * rexp (a * x) + log (a * rexp (a * x)) ≥ (a * x + 2) + log (a * x + 2) := by
    intro x hx; specialize h x
    have q : a * rexp (a * x) - log (x + 2 / a) - 2 ≥ 0 := h hx
    have q' : log (a * x + 2) - log a = log (x + 2 / a) := by
      have : x + 2 / a = (a * x + 2) / a := by
        ring_nf; simp only [add_left_inj]
        exact (eq_mul_inv_iff_mul_eq₀ ha).mpr rfl
      rw [this]; refine Eq.symm (log_div ?hx ha)
      have : x ≠ -2 / a := by linarith
      have r : a * x ≠ -2 / a * a := by nlinarith
      have : -2 / a * a = -2 := div_mul_cancel₀ (-2) ha
      rw [this] at r
      have : a * x + 2 ≠ -2 + 2 := (add_ne_add_left 2).mpr r
      simp only [neg_add_cancel] at this; exact this
    have l : a * rexp (a * x) - (log (a * x + 2) - log a) - 2 = a * rexp (a * x) - log (a * x + 2) + (log a + a * x) - 2 - a * x := by ring
    have : log a + a * x = log (a * rexp (a * x)) := by
      have : a * x = log (rexp (a * x)) := Eq.symm (log_exp (a * x))
      nth_rw 1 [this]; refine Eq.symm (log_mul ha ?hy)
      exact exp_ne_zero (a * x)
    rw [← q', l, this] at q; linarith
  -- rearrange the inequality into $f$-terms, and take the $f$ away as it is monotone
  have g : ∀ x > -2 / a, f (a * rexp (a * x)) ≥ f (a * x + 2) := fun x a => g x a
  have mono' : ∀ x > -2 / a, a * rexp (a * x) ≥ a * x + 2 := by
    intro x h
    have p₁: a * x + 2 > 0 := by
      have m : a * x > -2 / a * a := by nlinarith
      have : -2 / a * a = -2 := div_mul_cancel₀ (-2) ha
      rw [this] at m; linarith
    have p₂ : a * rexp (a * x) > 0 := by refine mul_pos p ?_; exact exp_pos (a * x)
    exact le_imp_le_of_lt_imp_lt (mono p₂ p₁) (g x h)
  let g := fun x => rexp (a * x) - x - 2 / a
  have : ∀ x > -2 / a, g x ≥ 0 := by
    intro x h; unfold_let g
    have := mono' x h
    have : a * rexp (a * x) - a * x - 2 ≥ 0 := by linarith
    have : (a * rexp (a * x) - a * x - 2) / a ≥ 0 := div_nonneg this hyp
    have : (a * rexp (a * x) - a * x - 2) / a = rexp (a * x) - x - 2 / a := by ring_nf; rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ ha, one_mul, add_right_inj, sub_left_inj, mul_comm, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    simp only [ge_iff_le, sub_nonneg]
    linarith
  -- with the condition above we can simplify the problem to making sure that $func(x)$ is positive on the domain
  have checkpt: ∀ x > -2, func x ≥ 0 := by
    unfold_let func
    intro x h
    let y := x / a
    have trans : x = a * y := Eq.symm (mul_div_cancel₀ x ha)
    have : y > -2 / a := div_lt_div_of_pos_right h p
    simp_rw [ge_iff_le, sub_nonneg, trans]
    specialize mono' y this; linarith
  -- with $a>e^2$ it is easy to verify the result
  by_cases hyp : a ≥ rexp 2
  have : rexp 2 > rexp 1 := by norm_num
  linarith
  -- if not we can take in special value $func(-\ln a)$ for a check to get the desired result
  have king : - log a > -2 := by
    refine neg_lt_neg_iff.mpr ?_
    refine (log_lt_iff_lt_exp p).mpr ?_
    linarith
  specialize checkpt (-log a) king
  unfold_let func at checkpt; simp only [sub_neg_eq_add, ge_iff_le, sub_nonneg] at checkpt
  have king₁: rexp (-log a) = (rexp (log a))⁻¹ := exp_neg (log a)
  have king₂: rexp (log a) = a := exp_log p
  have : a * a⁻¹ = 1 := CommGroupWithZero.mul_inv_cancel a ha
  rw [king₁, king₂, this] at checkpt
  have : log a ≥ 1 := by linarith
  exact (le_log_iff_exp_le p).mp this
  -- for the other side we make similar transformation to keep things simple, and the focus of the problem is to prove that $func(x)$ is non-negative in its domain.
  intro hab x hx
  have : rexp 1 > 0 := exp_pos 1
  have l : a * x > a * (-2 / a) := by
    refine (mul_lt_mul_iff_of_pos_left ?a0).mpr hx
    linarith
  have : a * (-2 / a) = -2 := mul_div_cancel₀ (-2) (by linarith)
  rw [this] at l
  let P := a * x
  have over : P > -2 := l
  have ov : P ≥ -2 := by linarith
  have : a * rexp (a * x) - log (x + 2 / a) = a * rexp P - log ((P + 2) / a) := by
    unfold_let P; simp only [sub_right_inj]
    congr; ring_nf
    rw [mul_assoc, CommGroupWithZero.mul_inv_cancel a (by linarith), mul_one]
  rw [this]
  have : log ((P + 2) / a) = log (P + 2) - log a := by apply log_div; linarith; exact ha
  rw [this]; simp only [ge_iff_le, sub_nonneg, sub_sub]
  have : log (P + 2) + (P + 2) ≤ a * rexp P + log (a * rexp P) := by
    have kk : P + 2 ≤ a * rexp P := by
      have : func P ≥ 0 := by
        -- from the derivatives we can deduce $func(x)$ is antitone on $(-\infty,-\ln a)$
        have anti : StrictAntiOn func (Set.Iic (-log a)) := by
          apply strictAntiOn_of_deriv_neg
          exact convex_Iic (-log a)
          apply ContinuousOn.add
          apply ContinuousOn.add
          apply Continuous.comp_continuousOn'
          exact continuous_mul_left a
          exact continuousOn_exp
          exact continuousOn_neg
          exact continuousOn_const
          intro x h; simp only [interior_Iic, mem_Iic] at h
          rw [funcde]
          have m : rexp x < rexp (-log a) := exp_lt_exp.mpr h
          have m₁: rexp (-log a) = (rexp (log a))⁻¹ := exp_neg (log a)
          have : rexp (log a) = a := by apply exp_log; linarith
          rw [m₁, this] at m
          have : a * rexp x < a * a⁻¹ := (mul_lt_mul_left (by linarith)).mpr m
          have : a * a⁻¹ = 1 := CommGroupWithZero.mul_inv_cancel a ha
          linarith
        unfold StrictAntiOn at anti
        -- and it is monotone on $(-\ln a,\infty)$
        have mono : StrictMonoOn func (Set.Ici (-log a)) := by
          apply strictMonoOn_of_deriv_pos
          exact convex_Ici (-log a)
          apply ContinuousOn.add
          apply ContinuousOn.add
          apply Continuous.comp_continuousOn'
          exact continuous_mul_left a
          exact continuousOn_exp
          exact continuousOn_neg
          exact continuousOn_const
          intro x h; simp only [interior_Ici, mem_Ici_of_Ioi] at h
          rw [funcde]
          have m : rexp x > rexp (-log a) := exp_lt_exp.mpr h
          have m₁: rexp (-log a) = (rexp (log a))⁻¹ := exp_neg (log a)
          have : rexp (log a) = a := by apply exp_log; linarith
          rw [m₁, this] at m
          have : a * rexp x > a * a⁻¹ := (mul_lt_mul_left (by linarith)).mpr m
          have := CommGroupWithZero.mul_inv_cancel a ha
          linarith
        unfold StrictMonoOn at mono
        -- again we verify, since when $a\geqslant e^2$ we have $-\ln a < -2$, we only need to consider $func(-2)$ as minimum value
        by_cases hyp : a ≥ rexp 2
        have : (Set.Ici (-2)) ⊆ (Set.Ici (-log a)) := by
          refine GCongr.Ici_subset_Ici_of_le ?_; simp only [neg_le_neg_iff]; refine
            (le_log_iff_exp_le (by linarith)).mpr hyp
        have : StrictMonoOn func (Set.Ici (-2)) := StrictMonoOn.mono mono this
        unfold StrictMonoOn at this
        have po : (-2 : ℝ) ≤ -2 := by linarith
        simp only [mem_Ici] at this
        specialize this po ov over
        have : func (-2) > 0 := by
          unfold_let func; simp only [sub_neg_eq_add, add_sub_cancel_right]
          have : rexp (-2) > 0 := exp_pos (-2)
          nlinarith
        linarith
        -- when $e< a< e^2$ it comes from above that $x = -\ln a$ is point of minimum, and we check this value is non-negative
        have : -log a ≤ -log a := by linarith
        have ops: ∀ x, func x ≥ func (-log a) := by
          intro x
          by_cases hyp : x > -log a
          have j : x ≥ -log a := by linarith
          specialize mono this j hyp; linarith
          by_cases hyp : x = -log a; rw [hyp]
          have b: x < -log a := by
            by_contra p
            push_neg at p
            by_cases hyp' : x = -log a; contradiction
            have : x > -log a := lt_of_le_of_ne p fun a_1 => hyp (id (Eq.symm a_1))
            contradiction
          have j : x ≤ -log a := by linarith
          specialize anti j this b
          linarith
        have : func (-log a) ≥ 0 := by
          unfold_let func; simp only [sub_neg_eq_add, ge_iff_le, sub_nonneg]
          have d: rexp (-log a) = (rexp (log a))⁻¹ := exp_neg (log a)
          have : rexp (log a) = a := by refine exp_log ?hx
          rw [d, this, CommGroupWithZero.mul_inv_cancel a ha]
          have : log a ≥ log (rexp 1) := by apply log_le_log; exact exp_pos 1; linarith
          have : log (rexp 1) = 1 := log_exp 1
          linarith
        -- since for all value $x$ $func(x)$ is non-negative the desired result follows
        exact Preorder.le_trans 0 (func (-log a)) (func P) this (ops P)
      unfold_let func at this
      simp only [ge_iff_le, sub_nonneg] at this; linarith
    have u₁: P + 2 > 0 := by linarith
    have u₂: a * rexp P > 0 := gt_of_ge_of_gt kk u₁
    unfold StrictMonoOn at mono
    unfold_let f at mono
    by_cases hyp : P + 2 = a * rexp P; rw [hyp]; linarith
    have : P + 2 < a * rexp P := lt_of_le_of_ne kk hyp
    -- returning to the monotone property of $f$ we get the inequality desired
    specialize mono u₁ u₂ this
    simp only at mono
    linarith
  -- rearrange the inequality and we get the original one from the problem, thus closing the discussion
  have : log (a * rexp P) = log a + log (rexp P) := by refine log_mul ha ?hl; exact exp_ne_zero P
  have : log (rexp P) = P := log_exp P
  linarith