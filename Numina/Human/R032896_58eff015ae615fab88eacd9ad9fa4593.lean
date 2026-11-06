import Mathlib
open Real Complex Polynomial

/- Prove that for every $z \in \mathbb{C}$ such that $|z| < \frac{1}{2}$, the inequality $| \log{(1+z)} - z | \le |z|^2$ holds. -/
theorem inequalities_617622 (z : ℂ) (hz : ‖z‖ < 1 / 2) :
    ‖log (1 + z) - z‖ ≤ ‖z‖ ^ 2 := by
  -- 1. The logarithmic series expansion for $\log(1+z)$ is given by $\log(1+z) = \sum_{k=1}^\infty \frac{(-1)^{k+1}z^k}{k}$, valid for $|z| &lt; 1$.
  let f (k : ℕ) := if k = 0 then 0 else (-1) ^ (k + 1) * z ^ k / k
  have hsummable : Summable f := by
    apply Summable.of_norm
    unfold f
    let f (k : ℕ) := (1 / 2 : ℝ) ^ k
    apply Summable.of_nonneg_of_le (f := f)
    · intro _
      apply norm_nonneg
    · intro b
      by_cases hb : b = 0
      · simp [hb, f]
      · unfold f
        simp only [if_neg hb]
        rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
        apply div_le_iff₀ ?_ |>.mpr
        · trans (1 / 2 : ℝ) ^ b
          · gcongr
          · apply le_mul_of_one_le_right
            · apply pow_nonneg
              simp
            · simp
              exact Nat.one_le_iff_ne_zero.mpr hb
        · simp
          exact Nat.zero_lt_of_ne_zero hb
    · exact summable_geometric_two
  have hlog : log (1 + z) = ∑' k : ℕ, f k := by
    have hdiff : DifferentiableOn ℂ (fun x : ℂ => log (1 + x)) (Metric.ball 0 1)  := by
      apply DifferentiableOn.clog
      · apply DifferentiableOn.add
        · exact differentiableOn_const 1
        · exact differentiableOn_id'
      · intro x hx
        simp [Metric.mem_ball] at hx
        simp [slitPlane]
        left
        obtain h := Complex.abs_re_le_abs x
        have : |x.re| < 1 := by
          apply lt_of_le_of_lt h
          exact hx
        have : x.re > -1 := by exact neg_lt_of_abs_lt this
        exact neg_lt_iff_pos_add'.mp this
    have hz : z ∈ Metric.ball 0 1 := by
      simp [Metric.ball]
      simp at hz
      trans 2⁻¹
      · exact hz
      · norm_num
    have := Complex.taylorSeries_eq_on_ball hdiff hz
    rw [←this]
    congr
    ext n
    unfold f
    let s := slitPlane -ᵥ {1}
    have hs : ∀ x ∈ s, 1 + x ∈ slitPlane := by
      intro x hx
      simp [s] at hx
      obtain ⟨a, ha⟩ := hx
      simp [←ha.2]
      exact ha.1
    have huni_at_s {x : ℂ} (hx : x ∈ s) : UniqueDiffWithinAt ℂ s x := by
      refine UniqueDiffOn.uniqueDiffWithinAt ?_ hx
      unfold s
      refine IsOpen.uniqueDiffOn ?_
      apply IsOpen.sub_right
      exact Complex.isOpen_slitPlane
    -- compute the iterated derivative of the logarithm
    have (hn : n > 0) (x : ℂ) (hx : x ∈ s) : iteratedDerivWithin n (fun x ↦ Complex.log (1 + x)) s x = (-1) ^ (n + 1) * (n - 1).factorial * (1 / (1 + x) ^ n) := by
      induction n, hn using Nat.le_induction generalizing x
      · rw [iteratedDerivWithin_one (huni_at_s hx)]
        simp
        change derivWithin (Complex.log ∘ (fun x => 1 + x)) s x = (1 + x)⁻¹
        rw [derivWithin_comp (s' := slitPlane) (hxs := (huni_at_s hx)), derivWithin_add (huni_at_s hx), derivWithin_id' _ _ (huni_at_s hx)]
        · simp
          have : deriv Complex.log (1 + x) = (1 + x)⁻¹ := by
            trans deriv (Complex.log ∘ (fun x : ℂ => 1 + x)) x
            · rw [deriv_comp, deriv_const_add, deriv_id'']
              · simp
              · exact Complex.differentiableAt_log (hs x hx)
              · apply DifferentiableAt.add
                · exact differentiableAt_const 1
                · exact differentiableAt_id'
            · rw [Complex.deriv_log_comp_eq_logDeriv]
              simp [logDeriv]
              rw [deriv_const_add, deriv_id'']
              · simp
              . apply DifferentiableAt.add
                · exact differentiableAt_const 1
                · exact differentiableAt_id'
              · exact hs x hx
          rw [←this]
          refine derivWithin_of_isOpen ?_ ?_
          · exact isOpen_slitPlane
          · exact hs x hx
        · exact differentiableWithinAt_const 1
        · exact differentiableWithinAt_id'
        · refine DifferentiableAt.differentiableWithinAt ?_
          apply DifferentiableAt.clog
          exact differentiableAt_id'
          exact hs x hx
        · change DifferentiableWithinAt ℂ (fun x ↦ id (1 + x)) s x
          refine (differentiableWithinAt_const_add_iff 1).mpr ?_
          exact differentiableWithinAt_id'
        · intro x hx
          simp
          exact hs x hx
      · rename_i n hn ih
        have : derivWithin (iteratedDerivWithin n (fun x ↦ Complex.log (1 + x)) s) s x = derivWithin (fun x : ℂ => (-1) ^ (n + 1) * (n - 1).factorial * (1 / (1 + x) ^ n)) s x := by
          apply derivWithin_congr
          · intro x hx
            rw [ih _ hx]
          · rw [ih _ hx]
        have hne : 1 + x ≠ 0 := by
          intro h
          apply hs at hx
          simp [h] at hx
        rw [iteratedDerivWithin_succ (huni_at_s hx), this]
        rw [derivWithin_const_mul (huni_at_s hx), derivWithin_div]
        · simp
          change (-1) ^ (n + 1) * ↑(n - 1).factorial * (-derivWithin ((fun x => x ^ n) ∘ (fun x : ℂ ↦ 1 + x)) s x / ((1 + x) ^ n) ^ 2) = (-1) ^ (n + 1 + 1) * ↑n.factorial * ((1 + x) ^ (n + 1))⁻¹
          rw [derivWithin_comp (s' := slitPlane) (hxs := (huni_at_s hx)), derivWithin_pow, derivWithin_add (huni_at_s hx)]
          simp
          · rw [derivWithin_id' _ _ (huni_at_s hx)]
            have : n.factorial = n * (n - 1).factorial := by
              nth_rw 1 [show n = n - 1 + 1 by rw [Nat.sub_add_cancel]; exact hn]
              rw [Nat.factorial_succ]
              rw [Nat.sub_add_cancel]
              exact hn
            rw [this]
            field_simp
            rw [pow_succ (-1) (n + 1)]
            rw [←pow_mul, show n * 2 = n + 1 + (n - 1) by rw [←Nat.add_sub_assoc]; ring_nf; rw [Nat.add_sub_cancel_left]; exact hn]
            rw [pow_add _ (n + 1)]
            ring
          · exact differentiableWithinAt_const 1
          · exact differentiableWithinAt_id'
          · refine UniqueDiffOn.uniqueDiffWithinAt ?_ ?_
            · refine IsOpen.uniqueDiffOn ?_
              exact Complex.isOpen_slitPlane
            · exact hs x hx
          · exact differentiableWithinAt_pow n
          · change DifferentiableWithinAt ℂ (fun x ↦ id (1 + x)) s x
            refine (differentiableWithinAt_const_add_iff 1).mpr ?_
            exact differentiableWithinAt_id'
          · intro x hx
            simp
            exact hs x hx
        · exact differentiableWithinAt_const 1
        · refine (differentiableWithinAt_comp_add_left 1).mpr ?_
          refine DifferentiableAt.differentiableWithinAt ?_
          apply DifferentiableAt.pow
          exact differentiableAt_id'
        · intro h
          have : ‖(1 + x) ^ n‖ = 0 := by rw [h]; simp
          rw [norm_pow] at this
          simp at this
          apply hs at hx
          rw [this.1] at hx
          simp at hx
        · refine UniqueDiffOn.uniqueDiffWithinAt ?_ hx
          unfold s
          refine IsOpen.uniqueDiffOn ?_
          apply IsOpen.sub_right
          exact Complex.isOpen_slitPlane
        · refine DifferentiableWithinAt.div ?_ ?_ ?_
          · exact differentiableWithinAt_const 1
          · refine (differentiableWithinAt_comp_add_left 1).mpr ?_
            refine DifferentiableAt.differentiableWithinAt ?_
            apply DifferentiableAt.pow
            exact differentiableAt_id'
          · intro h
            have : ‖(1 + x) ^ n‖ = 0 := by rw [h]; simp
            rw [norm_pow] at this
            simp at this
            apply hs at hx
            rw [this.1] at hx
            simp at hx
    have (hn : n > 0) : iteratedDeriv n (fun x ↦ Complex.log (1 + x)) 0 = (-1) ^ (n + 1) * (n - 1).factorial := by
      obtain h := this hn 0 (by simp [s]; use 1; simp)
      simp at h
      rw [←h, eq_comm]
      simp [iteratedDerivWithin]
      rw [iteratedFDerivWithin_eq_iteratedFDeriv]
      · rfl
      · refine IsOpen.uniqueDiffOn ?_
        apply IsOpen.sub_right
        exact Complex.isOpen_slitPlane
      · refine ContDiffAt.comp' ?_ ?_
        · refine Complex.contDiffAt_log ?_
          simp
        · apply ContDiffAt.add
          · exact contDiffAt_const
          · exact contDiffAt_id'
      · simp [s]
        use 1
        simp
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
      rw [this]
      nth_rw 1 [show n = n - 1 + 1 by exact Eq.symm (Nat.succ_pred_eq_of_ne_zero hn)]
      rw [Nat.factorial_succ]
      have : ((n - 1).factorial : ℂ) ≠ 0:= by
        norm_cast
        apply ne_of_gt
        positivity
      have : (n : ℂ) ≠ 0 := by norm_cast
      field_simp
      ring
      positivity
  -- 2. We need to evaluate the expression $| \log{(1+z)} - z |$.
  -- 3. Substituting the series expansion,
  -- we have: [ \log(1+z) - z = \sum_{k=1}^\infty \frac{(-1)^{k+1}z^k}{k} - z = \sum_{k=2}^\infty \frac{(-1)^{k+1}z^k}{k} ]
  have hsub : log (1 + z) - z = ∑' k : ℕ, (-1) ^ (k + 3) * z ^ (k + 2) / (k + 2) := by
    rw [hlog, tsum_eq_zero_add, tsum_eq_zero_add]
    · unfold f
      simp
      congr
      ext i
      ring
    · let i := Nat.succ
      change Summable (f ∘ i)
      apply Summable.comp_injective hsummable
      unfold i
      exact Nat.succ_injective
    · exact hsummable
  -- 4. Taking the absolute value, we get: [ \left| \log(1+z) - z \right| = \left| \sum_{k=2}^\infty \frac{(-1)^{k+1}z^k}{k} \right| ]
  -- 5. Using the triangle inequality, we can bound this by: [ \left| \sum_{k=2}^\infty \frac{(-1)^{k+1}z^k}{k} \right| \leq \sum_{k=2}^\infty \left| \frac{(-1)^{k+1}z^k}{k} \right| = \sum_{k=2}^\infty \frac{|z|^k}{k} ]
  -- 6. Factor out $|z|^2$ from the series: [ \sum_{k=2}^\infty \frac{|z|^k}{k} = |z|^2 \sum_{k=2}^\infty \frac{|z|^{k-2}}{k} ]
  have hnorm : ‖log (1 + z) - z‖ ≤ ‖z‖ ^ 2 * ∑' k : ℕ, ‖z‖ ^ k / (k + 2) := by
    rw [hsub]
    apply le_trans (norm_tsum_le_tsum_norm _)
    · apply le_of_eq
      rw [←tsum_mul_left]
      congr
      ext i
      rw [norm_div, norm_mul, norm_pow, norm_pow, pow_add, pow_add, norm_neg, norm_one, one_pow, one_pow, one_mul, one_mul, mul_comm]
      norm_cast
      ring
    · let i (a : ℕ) := a + 2
      have : (fun i : ℕ ↦ ‖(-1) ^ (i + 3) * z ^ (i + 2) / (↑i + 2)‖) = fun x => ‖(f ∘ i) x‖ := by
        ext x
        congr
        unfold i
        norm_cast
      rw [this]
      apply Summable.norm
      apply Summable.comp_injective hsummable
      unfold i
      exact add_left_injective 2
  -- 7. Re-index the series by letting $j = k - 2$: [ \sum_{k=2}^\infty \frac{|z|^{k-2}}{k} = \sum_{j=0}^\infty \frac{|z|^j}{j+2} ]
  apply le_trans hnorm
  apply mul_le_of_le_one_right (sq_nonneg _)
  -- 8. Since $|z| &lt; \frac{1}{2}$, we have: [ \sum_{j=0}^\infty \frac{|z|^j}{j+2} \leq \sum_{j=0}^\infty \frac{1}{2^j \cdot 2} = \frac{1}{2} \sum_{j=0}^\infty \frac{1}{2^j} ]
  trans (1 / 2) * ∑' (k : ℕ), (1 / 2 : ℝ) ^ k
  · rw [←tsum_mul_left]
    apply tsum_le_tsum
    · intro i
      trans (1 / 2 : ℝ) ^ i / (i + 2)
      · gcongr
      · apply div_le_iff₀ ?_ |>.mpr
        · nth_rw 2 [mul_comm]
          rw [mul_assoc]
          apply le_mul_of_one_le_right
          · apply pow_nonneg
            simp
          · norm_cast
            field_simp
            apply le_div_iff₀ ?_ |>.mpr
            · simp
            · simp
        · norm_cast
          simp
    · let f (k : ℕ) := (1 / 2 : ℝ) ^ k
      apply Summable.of_nonneg_of_le (f := f)
      · intro _
        positivity
      · intro i
        unfold f
        trans (1 / 2 : ℝ) ^ i / (i + 2)
        · gcongr
        · apply div_le_iff₀ ?_ |>.mpr
          · apply le_mul_of_one_le_right
            · apply pow_nonneg
              simp
            · norm_cast
              simp
          · norm_cast
            simp
      · exact summable_geometric_two
    · apply Summable.mul_left
      exact summable_geometric_two
  · -- 9. The geometric series $\sum_{j=0}^\infty \frac{1}{2^j}$ converges to 2: [ \sum_{j=0}^\infty \frac{1}{2^j} = 2 ]
    -- 10. Therefore: [ \sum_{j=0}^\infty \frac{1}{2^j \cdot 2} = \frac{1}{2} \cdot 2 = 1 ]
    apply le_of_eq
    rw [tsum_geometric_two]
    norm_num
