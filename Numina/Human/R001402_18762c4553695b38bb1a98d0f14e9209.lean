import Mathlib

open Real

noncomputable def f : ℝ → ℝ := fun x => log (x +1) / log x 

lemma fneg1 : x > 0 → x < 1 → f x < 0 := by
  intro h1 h2
  unfold f
  have pos1 : log (x + 1) > 0 := by 
    refine (log_pos_iff ?_).mpr ?_
    linarith
    linarith
  have neg1 : log x < 0 := by
    exact log_neg h1 h2
  exact div_neg_of_pos_of_neg pos1 neg1

lemma fpos1 : 0 < x → x > 1 → f x > 0 := by 
  intro h1 h2
  unfold f
  have pos1 : log x > 0 := by
    refine (log_pos_iff ?_).mpr ?_
    linarith
    linarith
  have pos2 : log (x + 1) > 0 := by
    refine (log_pos_iff ?_).mpr ?_
    linarith
    linarith
  exact div_pos pos2 pos1

lemma fmono1 : StrictAntiOn f (Set.Ioi 1) := by
  unfold f
  refine strictAntiOn_of_deriv_neg ?_ ?_ ?_
  exact convex_Ioi 1
  apply ContinuousOn.div₀
  refine ContinuousOn.log ?_ ?_
  apply ContinuousOn.add
  exact continuousOn_id' (Set.Ioi 1)
  exact continuousOn_const
  intro x hx
  simp at hx
  linarith
  apply ContinuousOn.log
  exact continuousOn_id' (Set.Ioi 1)
  intro x hx
  simp at hx
  linarith
  intro x hx
  simp at hx
  have pos : log x > 0 := by 
    exact log_pos hx
  linarith
  intro x hx
  rw [deriv_div, deriv_log, deriv_comp_add_const, deriv_log]
  have ineq1 : ((x + 1)⁻¹ * log x - log (x + 1) * x⁻¹) < 0 := by  
    have aux : (x + 1)⁻¹ * log x < log (x + 1) * x⁻¹ := by 
      rw [mul_comm]
      have aux1 : (x + 1)⁻¹ < x⁻¹ := by 
        simp at hx
        refine (inv_lt_inv₀ ?_ ?_).mpr ?_
        linarith
        linarith
        linarith
      have aux2 : log x < log (x + 1) := by
        refine log_lt_log ?_ ?_
        simp at hx
        linarith
        linarith
      refine mul_lt_mul aux2 (by linarith) ?_ ?_
      simp at hx
      positivity
      refine log_nonneg ?_
      simp at hx
      linarith
    linarith
  have ineq2 : log x ^ 2 > 0 := by 
    refine sq_pos_of_pos ?_
    simp at hx
    exact log_pos hx
  exact div_neg_of_neg_of_pos ineq1 ineq2
  refine DifferentiableAt.log ?_ ?_
  refine DifferentiableAt.add_const ?_ 1
  exact differentiableAt_id'
  simp at hx
  linarith
  refine differentiableAt_log ?_
  simp at hx
  linarith
  simp at hx
  have pos : log x > 0 := by 
    exact log_pos hx
  linarith

lemma fmono2 : AntitoneOn f (Set.Ioi 1) := by
  refine StrictAntiOn.antitoneOn ?_
  exact fmono1


lemma fmono3 : StrictAntiOn f (Set.Ioo 0 1) := by
  unfold f
  refine strictAntiOn_of_deriv_neg ?_ ?_ ?_
  exact convex_Ioo 0 1
  apply ContinuousOn.div₀
  refine ContinuousOn.log ?_ ?_
  apply ContinuousOn.add
  exact continuousOn_id' (Set.Ioo 0 1)
  exact continuousOn_const
  intro x hx
  simp at hx
  linarith
  apply ContinuousOn.log
  exact continuousOn_id' (Set.Ioo 0 1)
  intro x hx
  simp at hx
  linarith
  intro x hx
  simp at hx
  have pos : log x < 0 := by 
    apply log_neg
    exact hx.1
    exact hx.2
  linarith
  intro x hx
  rw [deriv_div, deriv_log, deriv_comp_add_const, deriv_log]
  have ineq1 : ((x + 1)⁻¹ * log x - log (x + 1) * x⁻¹) < 0 := by  
    have aux : (x + 1)⁻¹ * log x < log (x + 1) * x⁻¹ := by 
      rw [mul_comm]
      have aux1 : (x + 1)⁻¹ * log x < 0 := by 
        have aux3 : (x + 1)⁻¹ > 0 := by 
          have aux4 : x + 1 > 0 := by 
            simp at hx
            linarith [hx.1]
          positivity
        have aux4 : log x < 0 := by
          simp at hx
          exact log_neg hx.1 hx.2
        exact mul_neg_of_pos_of_neg aux3 aux4
      have aux2 : log (x + 1) * x⁻¹ > 0 := by
        have aux3 : log (x + 1) > 0 := by
          refine (log_pos_iff ?_).mpr ?_
          simp at hx
          linarith [hx.1]
          simp at hx
          linarith [hx.1]
        have aux4 : x⁻¹ > 0 := by
          have aux4 : x > 0 := by 
            simp at hx
            linarith [hx.1]
          positivity
          
        positivity
      linarith
    linarith
  have ineq2 : log x ^ 2 > 0 := by 
    simp at hx
    refine pow_two_pos_of_ne_zero ?_
    refine log_ne_zero_of_pos_of_ne_one ?_ ?_
    linarith [hx.1]
    linarith [hx.1]
  exact div_neg_of_neg_of_pos ineq1 ineq2
  refine DifferentiableAt.log ?_ ?_
  refine DifferentiableAt.add_const ?_ 1
  exact differentiableAt_id'
  simp at hx
  linarith
  refine differentiableAt_log ?_
  simp at hx
  linarith
  simp at hx
  have pos : log x < 0 := by 
    exact log_neg hx.1 hx.2
  linarith

lemma fmono4 : AntitoneOn f (Set.Ioo 0 1) := by
  refine StrictAntiOn.antitoneOn ?_
  exact fmono3


/- 20. (USA 2) Determine all pairs $(a, b)$ of positive real numbers with $a \neq 1$ such that  $$ \log _{a} b<\log _{a+1}(b+1) $$  ### 3.26 The Twenty-Sixth IMO -/
theorem algebra_23929 :
    {(a, b) : ℝ × ℝ | 0 < a ∧ 0 < b ∧ a ≠ 1 ∧ logb a b < logb (a + 1) (b + 1)} = 
    {(a, b) : ℝ × ℝ | b = 1 ∧ a ≠ 1 ∧ a > 0} ∪  {(a, b): ℝ × ℝ| a > b ∧ b > 1}
    ∪  {(a, b): ℝ × ℝ| a > 0 ∧ 1 > a ∧ b > 1} ∪  {(a, b): ℝ × ℝ| a > 0 ∧ b > a ∧ 1 > b} 
    ∪  {(a, b): ℝ × ℝ| b > 0 ∧ b < 1 ∧ 1 < a} := by 
  ext ⟨a, b⟩
  have eq1 (x y : ℝ) : logb x y = log y / log x := by simp [logb]
  constructor
  · -- forward direction
    simp
    intro apos bpos aneq h
    by_cases hb : b = 1
    -- the case b = 1
    · left; left; left; left
      exact ⟨hb, aneq, apos⟩
    -- the case b > 1 
    by_cases hbgt1 : b > 1 
    · 
      -- discuss whether a > 1
      by_cases hagt1 : a > 1
      · 
        rw [eq1, eq1] at h
        have blta : b < a := by
          by_contra hc
          simp at hc
          have fle : f a ≥ f b := by 
            obtain h1 := fmono2 
            unfold AntitoneOn at h1
            exact h1 (by simp; linarith) (by simp; linarith) hc
          unfold f at fle
          have hc1 : log b / log a ≥  log (b + 1) / log (a + 1) := by 
            refine (div_le_div_iff₀ ?_ ?_).mpr ?_
            exact (log_pos_iff (by linarith)).mpr (by linarith)
            exact (log_pos_iff (by linarith)).mpr (by linarith)
            nth_rw 2 [mul_comm]
            refine (div_le_div_iff₀ ?_ ?_).mp fle
            exact (log_pos_iff (by linarith)).mpr (by linarith)
            exact (log_pos_iff (by linarith)).mpr (by linarith)
          linarith
        left; left; left; right
        exact ⟨blta, hbgt1⟩
      · -- the case a < 1
        have alt1 : a < 1 := by 
          simp at hagt1
          exact lt_of_le_of_ne hagt1 aneq
        left; left; right
        exact ⟨apos, alt1, hbgt1⟩
    · -- the case b < 1
      have hblt1 : b < 1 := by 
        simp at hbgt1
        exact lt_of_le_of_ne hbgt1 hb
      by_cases hagt1 : a > 1
      · -- the case a > 1 
        right 
        exact ⟨bpos, hblt1, hagt1⟩
      · -- the case a < 1
        have alt1 : a < 1 := by 
          simp at hagt1
          exact lt_of_le_of_ne hagt1 aneq
        left; right
        rw [eq1, eq1] at h
        have altb : a < b := by 
          by_contra hc 
          simp at hc
          obtain h1 := fmono4 
          unfold AntitoneOn at h1
          have ain : a ∈ Set.Ioo 0 1 := by 
            simp
            exact ⟨apos, alt1⟩
          have bin : b ∈ Set.Ioo 0 1 := by 
            simp
            exact ⟨bpos, hblt1⟩
          obtain h2 := h1 bin ain hc
          unfold f at h2
          have hc1 : log b / log a ≥  log (b + 1) / log (a + 1) := by 
            refine (mul_sub_mul_div_mul_nonpos_iff ?_ ?_).mp ?_
            refine log_ne_zero_of_pos_of_ne_one ?_ ?_
            linarith
            linarith
            refine log_ne_zero_of_pos_of_ne_one ?_ ?_
            linarith
            linarith
            
            have aux1 : log a ≠ 0 := by 
              refine log_ne_zero_of_pos_of_ne_one ?_ ?_
              linarith
              linarith
            have aux2 : log b ≠ 0 := by 
              refine log_ne_zero_of_pos_of_ne_one ?_ ?_
              linarith
              linarith
            obtain h3 := (mul_sub_mul_div_mul_nonpos_iff aux1 aux2).mpr h2
            have aux3 : (log a * log b) > 0 := by 
              have aux4 : log a < 0 := by
                exact log_neg apos alt1
              have aux5 : log b < 0 := by
                exact log_neg bpos hblt1
              exact mul_pos_of_neg_of_neg aux4 aux5
            have aux4 : (log (b + 1) * log a - log b * log (a + 1)) ≥  0 := by 
              obtain h4 := (div_le_iff₀ aux3).mp h3
              simp at h4
              linarith
            have ineq2 : (log (a + 1) * log a) < 0 := by 
              have aux4 : log a < 0 := by 
                exact log_neg apos alt1
              have aux5 : log (a + 1) > 0 := by 
                apply log_pos
                linarith
              exact mul_neg_of_pos_of_neg aux5 aux4
            refine (div_le_iff_of_neg ineq2).mpr ?_
            simp
            linarith
          linarith
        simp at hbgt1
        have blt1 : b < 1 := by 
          exact lt_of_le_of_ne hbgt1 hb
        exact ⟨apos, altb, blt1⟩
  · -- backward direction
    intro h
    simp at h
    -- divide into five cases, and check for each case 
    obtain h1 | h5 := h 
    obtain h1 | h4  := h1
    obtain h1 | h3 := h1
    obtain h1 | h2 := h1
    · -- the case : b = 1 ∧ ¬a = 1 ∧ 0 < a
      simp
      obtain ⟨hb, ha, hapos⟩ := h1
      constructor
      exact hapos
      constructor
      linarith
      constructor
      exact ha
      rw [eq1, eq1]
      simp [hb]
      have pos1 : log (a + 1) > 0 := by 
        apply log_pos
        linarith
      positivity
    · -- the case : b < a ∧ 1 < b
      obtain ⟨blta, bgt1⟩ := h2
      simp
      constructor
      linarith
      constructor
      linarith
      constructor
      linarith
      rw [eq1, eq1]
      obtain aux := fmono1
      unfold StrictAntiOn at aux
      obtain aux1 := aux (by simp; linarith) (by simp; linarith) blta
      unfold f at aux1
      refine (div_lt_div_iff₀ ?_ ?_).mpr ?_
      · apply log_pos
        linarith
      · apply log_pos
        linarith
      obtain aux2 := (div_lt_div_iff₀ (log_pos (by linarith)) (log_pos (by linarith))).mp aux1
      linarith
    · -- the case :0 < a ∧  a < 1 ∧ 1 < b
      simp
      obtain ⟨apos, alt1, bgt1⟩ := h3
      constructor
      linarith
      constructor
      linarith
      constructor
      linarith
      rw [eq1, eq1]
      have neg1 : log b / log a < 0 := by 
        have aux1 : log b > 0 := by 
          exact log_pos (by linarith)
        have aux2 : log a < 0 := by 
          exact log_neg apos alt1
        exact div_neg_of_pos_of_neg aux1 aux2
      have pos1 : log (b + 1) / log (a + 1) > 0 := by
        have aux1 : log (b + 1) > 0 := by 
          exact log_pos (by linarith)
        have aux2 : log (a + 1) > 0 := by 
          exact log_pos (by linarith)
        positivity
      linarith
    · -- the case : 0 < a ∧ a < b ∧ b < 1
      obtain ⟨apos, altb, blt1⟩ := h4
      simp
      constructor
      linarith
      constructor
      linarith
      constructor
      linarith
      rw [eq1, eq1]
      obtain aux1 := fmono3
      unfold StrictAntiOn at aux1
      have ain : a ∈ Set.Ioo 0 1 := by 
            simp
            exact ⟨apos, (by linarith)⟩
      have bin : b ∈ Set.Ioo 0 1 := by 
        simp
        exact ⟨(by linarith), blt1⟩
      obtain aux2 := aux1 ain bin altb
      unfold f at aux2
      refine (mul_sub_mul_div_mul_neg_iff ?_ ?_).mp ?_
      · refine log_ne_zero_of_pos_of_ne_one apos ?_
        linarith
      · refine log_ne_zero_of_pos_of_ne_one ?_ ?_
        linarith
        linarith
      · 
        have neq1 : log b ≠ 0 := by 
          refine log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
        have neq2 : log a ≠ 0 := by 
          refine log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
        obtain aux3 := (mul_sub_mul_div_mul_neg_iff neq1 neq2).mpr aux2
        have neg1 : log (a + 1) * log a < 0 := by
          have aux4 : log (a + 1) > 0 := by 
            exact log_pos (by linarith)
          have aux5 : log a < 0 := by
            exact log_neg apos (by linarith)
          exact mul_neg_of_pos_of_neg aux4 aux5
        refine (div_lt_iff_of_neg ?_).mpr ?_
        linarith
        simp 
        have aux4 : (log b * log a) > 0 := by 
          have neg1 : log b < 0 := by 
            exact log_neg (by linarith) (by linarith)
          have neg2 : log a < 0 := by
            exact log_neg apos (by linarith)
          exact mul_pos_of_neg_of_neg neg1 neg2
        obtain aux5 := (div_lt_iff₀ aux4).mp aux3
        simp at aux5
        linarith
    · -- the case : 0 < b ∧ b < 1 ∧ 1 < a
      obtain ⟨bpos, blt1, agt1⟩ := h5
      simp
      constructor
      linarith
      constructor
      linarith
      constructor
      linarith
      rw [eq1, eq1]
      have neg : log b / log a < 0 := by 
        have neg1 : log b < 0 := by 
          exact log_neg (by linarith) (by linarith)
        have pos1 : log a > 0 := by
          exact log_pos (by linarith)
        exact div_neg_of_neg_of_pos neg1 pos1
      have pos1 : log (b + 1) / log (a + 1) > 0 := by
        have pos2 : log (b + 1) > 0 := by
          exact log_pos (by linarith)
        have pos3 : log (a + 1) > 0 := by
          exact log_pos (by linarith)
        positivity
      linarith