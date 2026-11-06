import Mathlib

/- Example 21 Positive numbers $a, b, c$ satisfy $a+b+c=1$, prove that: $\frac{1+a}{1-a}+\frac{1+b}{1-b}+$ $\frac{1+c}{1-c} \leqslant 2\left(\frac{b}{a}+\frac{c}{b}+\frac{a}{c}\right)$. (2004 Japan Mathematical Olympiad Problem) -/
theorem inequalities_600892
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a + b + c = 1) :
    (1 + a) / (1 - a) + (1 + b) / (1 - b) + (1 + c) / (1 - c) ≤
    2 * (b / a + c / b + a / c) := by

  rw [←h]
  -- apply the rearrangement inequality to prove that 
  -- ab^2 + bc^2 + ca^2 ≤ (bc)^2 / a + (ca)^2 / b + (ab)^2 / c
  -- a^2b + b^2c + c^2a ≤ (bc)^2 / a + (ca)^2 / b + (ab)^2 / c
  have rearrangement_inequality : a * b ^ 2 + b * c ^ 2 + c * a ^ 2 ≤ (b * c) ^ 2 / a +  (c * a) ^ 2 / b + (a * b) ^ 2 / c
      ∧ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a ≤ (b * c) ^ 2 / a +  (c * a) ^ 2 / b + (a * b) ^ 2 / c := by
    clear h
    -- w.l.o.g. we can assume that a ≤ b ≤ c
    wlog h : a ≤ b ∧ b ≤ c with H
    · simp at h
      by_cases hab : a ≤ b
      · obtain h := h hab
        by_cases hca : c ≤ a
        · obtain ⟨h₁, h₂⟩ := H c a b hc ha hb ⟨hca, hab⟩
          split_ands
          · apply le_of_eq_of_le ?_ (le_of_le_of_eq h₁ ?_) <;> ring
          · apply le_of_eq_of_le ?_ (le_of_le_of_eq h₂ ?_) <;> ring
        · simp at hca
          obtain ⟨h₁, h₂⟩ := H a c b ha hc hb ⟨le_of_lt hca, le_of_lt h⟩
          split_ands
          · apply le_of_eq_of_le ?_ (le_of_le_of_eq h₂ ?_) <;> ring
          · apply le_of_eq_of_le ?_ (le_of_le_of_eq h₁ ?_) <;> ring
      · simp at hab
        by_cases hcb : c ≤ b
        · obtain ⟨h₁, h₂⟩ := H c b a hc hb ha ⟨hcb, le_of_lt hab⟩
          split_ands
          · apply le_of_eq_of_le ?_ (le_of_le_of_eq h₂ ?_) <;> ring
          · apply le_of_eq_of_le ?_ (le_of_le_of_eq h₁ ?_) <;> ring
        · simp at hcb
          by_cases hac : a ≤ c
          · obtain ⟨h₁, h₂⟩ := H b a c hb ha hc ⟨le_of_lt hab, hac⟩
            split_ands
            · apply le_of_eq_of_le ?_ (le_of_le_of_eq h₂ ?_) <;> ring
            · apply le_of_eq_of_le ?_ (le_of_le_of_eq h₁ ?_) <;> ring
          · simp at hac
            obtain ⟨h₁, h₂⟩ := H b c a hb hc ha ⟨le_of_lt hcb, le_of_lt hac⟩
            split_ands
            · apply le_of_eq_of_le ?_ (le_of_le_of_eq h₁ ?_) <;> ring
            · apply le_of_eq_of_le ?_ (le_of_le_of_eq h₂ ?_) <;> ring
    · -- apply the rearrangement inequality
      obtain ⟨hab, hbc⟩ := h
      let f (i : Fin 3) := 
          match i with
          | 0 => 1 / a
          | 1 => 1 / b
          | 2 => 1 / c
      let g (i : Fin 3) :=
        match i with
        | 0 => (b * c) ^ 2
        | 1 => (c * a) ^ 2
        | 2 => (a * b) ^ 2
      have hfg : Monovary f g := by
        refine Antitone.monovary ?_ ?_
        · intro i j h
          fin_cases i
          all_goals
            fin_cases j
            any_goals
              simp at h ⊢
            all_goals
              simp [f]
              apply inv_le_inv₀ ?_ ?_ |>.mpr
              · linarith only [hab, hbc]
              all_goals positivity
        · intro i j h
          fin_cases i
          all_goals
            fin_cases j
            any_goals
              simp at h ⊢
            all_goals
              simp [g]
              apply pow_le_pow_left₀
              · positivity
              · nlinarith
      split_ands
      · let σ : Equiv.Perm (Fin 3) := by
          apply Equiv.mk (![2, 0, 1]) (![1, 2, 0])
          · intro i
            fin_cases i
            all_goals
              simp
          · intro i
            fin_cases i
            all_goals
              simp
        obtain h := Monovary.sum_mul_comp_perm_le_sum_mul (σ := σ) hfg
        simp [Fin.sum_univ_three, f, g, σ] at h
        apply le_of_eq_of_le ?_ (le_of_le_of_eq h ?_)
        · field_simp
          ring
        · field_simp
      · let σ : Equiv.Perm (Fin 3) := by
          apply Equiv.mk (![1, 2, 0]) (![2, 0, 1])
          · intro i
            fin_cases i
            all_goals
              simp
          · intro i
            fin_cases i
            all_goals
              simp
        obtain h := Monovary.sum_mul_comp_perm_le_sum_mul (σ := σ) hfg
        simp [Fin.sum_univ_three, f, g, σ] at h
        apply le_of_eq_of_le ?_ (le_of_le_of_eq h ?_)
        · field_simp
          ring
        · field_simp
  -- then we have a^2bc^3 + b^2ca^3 + c^2ab^3 ≤ b^3c^3 + c^3a^3 + a^3b^3
  have order_inequality1 : a ^ 2 * b * c ^ 3 + b ^ 2 * c * a ^ 3 + c ^ 2 * a * b ^ 3 ≤ b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3 + a ^ 3 * b ^ 3 := by
    obtain h := mul_le_mul_of_nonneg_left rearrangement_inequality.2 (show 0 ≤ a * b * c by positivity)
    apply le_of_eq_of_le ?_ (le_of_le_of_eq h ?_)
    · ring
    · field_simp
      ring
  -- and a^3b^2c + b^3c^2a + c^3a^2b ≤ b^3c^3 + c^3a^3 + a^3b^3
  have order_inequality2 : a ^ 3 * b * c ^ 2 + b ^ 3 * c * a ^ 2 + c ^ 3 * a * b ^ 2 ≤ b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3 + a ^ 3 * b ^ 3 := by
    obtain h := mul_le_mul_of_nonneg_left rearrangement_inequality.1 (show 0 ≤ a * b * c by positivity)
    apply le_of_eq_of_le ?_ (le_of_le_of_eq h ?_)
    · ring
    · field_simp
      ring
  -- We can use the AM-GM inequality to prove that
  -- a^4b^2 + b^4c^2 + c^4a^2 ≥ 3a^2bc^2
  have am_gm : a ^ 4 * b ^ 2 + b ^ 4 * c ^ 2 + c ^ 4 * a ^ 2 ≥ 3 * a ^ 2 * b ^ 2 * c ^ 2 := by
    let w : ℝ := 1 / 3
    have hw : 0 ≤ w := by positivity
    have h₁ : a ^ 4 * b ^ 2 ≥ 0 := by positivity
    have h₂ : b ^ 4 * c ^ 2 ≥ 0 := by positivity
    have h₃ : c ^ 4 * a ^ 2 ≥ 0 := by positivity
    obtain h := Real.geom_mean_le_arith_mean3_weighted hw hw hw h₁ h₂ h₃ (by norm_num)
    unfold w at h
    field_simp at h
    apply le_div_iff₀ (by simp) |>.mp at h
    apply le_of_eq_of_le ?_ (le_of_le_of_eq h ?_)
    · rw [←Real.mul_rpow, ←Real.mul_rpow]
      ring_nf
      rw [Real.mul_rpow, Real.mul_rpow]
      rw [←Real.rpow_natCast _ 6, ←Real.rpow_natCast _ 6, ←Real.rpow_natCast _ 6]
      rw [←Real.rpow_mul, ←Real.rpow_mul, ←Real.rpow_mul]
      norm_num
      all_goals positivity
    · ring
  -- It is sufficient to prove that
  -- (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) ≤ b / a + c / b + a / c
  have h₁ : (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) ≤ b / a + c / b + a / c := by
    apply sub_nonneg.mp
    field_simp
    apply div_nonneg
    · -- add the first rearrangement inequality and the result obtained from AM-GM
      ring_nf
      apply add_le_add order_inequality1 at am_gm
      apply sub_nonneg.mpr at am_gm
      apply le_of_le_of_eq am_gm
      ring
    · positivity
  -- and (a + c) / (b + c) + (b + a) / (c + a) + (c + b) / (a + b) ≤ b / a + c / b + a / c
  have h₂ : (a + c) / (b + c) + (b + a) / (c + a) + (c + b) / (a + b) ≤ b / a + c / b + a / c := by
    apply sub_nonneg.mp
    field_simp
    apply div_nonneg
    · -- add the second rearrangement inequality and the result obtained from AM-GM
      ring_nf
      apply add_le_add order_inequality2 at am_gm
      apply sub_nonneg.mpr at am_gm
      apply le_of_le_of_eq am_gm
      ring
    · positivity
  -- Add the two inequalities, we are done.
  apply le_of_eq_of_le ?_ (le_of_le_of_eq (add_le_add h₁ h₂) ?_) <;> ring