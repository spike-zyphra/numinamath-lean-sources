import Mathlib

/- Let $a, b, c$ be positive real numbers. Prove that

$$
\left(\left(3 a^{2}+1\right)^{2}+2\left(1+\frac{3}{b}\right)^{2}\right)\left(\left(3 b^{2}+1\right)^{2}+2\left(1+\frac{3}{c}\right)^{2}\right)\left(\left(3 c^{2}+1\right)^{2}+2\left(1+\frac{3}{a}\right)^{2}\right) \geq 48^{3}
$$

When does equality hold? -/
theorem inequalities_605631 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((3 * a ^ 2 + 1) ^ 2 + 2 * (1 + 3 / b) ^ 2) * ((3 * b ^ 2 + 1) ^ 2 + 2 * (1 + 3 / c) ^ 2) * ((3 * c ^ 2 + 1) ^ 2 + 2 * (1 + 3 / a) ^ 2) ≥ 48 ^ 3 ∧
    (((3 * a ^ 2 + 1) ^ 2 + 2 * (1 + 3 / b) ^ 2) * ((3 * b ^ 2 + 1) ^ 2 + 2 * (1 + 3 / c) ^ 2) * ((3 * c ^ 2 + 1) ^ 2 + 2 * (1 + 3 / a) ^ 2) = 48 ^ 3 ↔ a = b ∧ b = c ∧ c = 1) := by
  -- Prove the AM-GM inequality for four variables.
  have AM_GM₄ (x y z w : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w) : (1 / 4 : ℝ) * x + (1 / 4 : ℝ) * y + (1 / 4 : ℝ) * z + (1 / 4 : ℝ) * w ≥ x ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ) * z ^ (1 / 4 : ℝ) * w ^ (1 / 4 : ℝ) := by
    apply Real.geom_mean_le_arith_mean4_weighted (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity) (by positivity) (by norm_num)
  -- Prove the AM-GM inequality for three variables.
  have AM_GM₃ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / 3 : ℝ) * x + (1 / 3 : ℝ) * y + (1 / 3 : ℝ) * z ≥ x ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ) * z ^ (1 / 3 : ℝ) := by
    apply Real.geom_mean_le_arith_mean3_weighted (by norm_num) (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity) (by norm_num)
  -- Prove the equality condition of AM-GM inequality for three variables.
  have AM_GM₃_eq (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / 3 : ℝ) * x + (1 / 3 : ℝ) * y + (1 / 3 : ℝ) * z = x ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ) * z ^ (1 / 3 : ℝ) ↔ x = y ∧ y = z := by
    -- Generalize x, y, z to s[0], s[1], s[2].
    let s (n : ℕ) :=
      match n with
      | 0 => x
      | 1 => y
      | 2 => z
      | _ => 0
    have hspos : ∀ i ∈ Finset.range 3, 0 ≤ s i := by
      intro i hi
      simp [s]
      match i with
      | 0 => exact (le_of_lt hx)
      | 1 => exact (le_of_lt hy)
      | 2 => exact (le_of_lt hz)
    -- Apply the theorem for equality case of AM-GM inequality.
    have := Real.geom_mean_eq_arith_mean_weighted_iff' (Finset.range 3) (fun n => 1 / 3) s (by simp) (by simp) hspos
    iterate 3 rw [Finset.sum_range_succ, Finset.prod_range_succ] at this
    rw [Finset.sum_range_zero, Finset.prod_range_zero] at this
    simp [s, -one_div] at this
    -- Match the form of the theorem and the goal we are trying to prove.
    apply Iff.intro
    . intro h
      symm at h
      rw [this] at h
      have h₀ := h 0 (by simp)
      have h₁ := h 1 (by simp)
      have h₂ := h 2 (by simp)
      simp [-one_div] at h₀ h₁ h₂
      exact ⟨by linarith, by linarith⟩
    . intro h
      symm
      rw [this]
      intro i hi
      match i with
      | 0 => linarith
      | 1 => linarith
      | 2 => linarith
  -- Show that 1 + 3x ≥ 4x ^ (3 / 4) for all positive x > 0.
  have h₀ (x : ℝ) (hx : 0 < x) : 1 + 3 * x ≥ 4 * x ^ (3 / 4 : ℝ) := by
    -- Apply the AM-GM inequality.
    specialize AM_GM₄ 1 x x x (by norm_num) hx hx hx
    rw [mul_assoc, <-Real.rpow_add hx, mul_assoc, <-Real.rpow_add hx, Real.one_rpow] at AM_GM₄
    linarith only [AM_GM₄]
  -- Show that (3x² + 1)² ≥ 16x³ for all positive x > 0.
  have h₁ (x : ℝ) (hx : 0 < x) : (3 * x ^ 2 + 1) ^ 2 ≥ 16 * x ^ 3 := by
    -- Use the lemma h₀ proved above.
    specialize h₀ (x ^ 2) (by positivity)
    nth_rw 2 [<-Real.rpow_natCast] at h₀
    rw [<-Real.rpow_mul (by positivity), ge_iff_le, <-sq_le_sq₀ (by positivity) (by positivity), mul_pow] at h₀
    nth_rw 2 [<-Real.rpow_natCast] at h₀
    rw [<-Real.rpow_mul (by positivity), add_comm] at h₀
    norm_num at h₀
    nth_rw 1 [show (3 : ℝ) = (3 : ℕ) by simp] at h₀
    rw [Real.rpow_natCast] at h₀
    linarith only [h₀]
  -- Show that 2(1 + 3 / x)² ≥ 32x ^ (-3 / 2).
  have h₂ (x : ℝ) (hx : 0 < x) : 2 * (1 + 3 / x) ^ 2 ≥ 32 * x ^ (-3 / 2 : ℝ) := by
    -- Use the lemma h₀ proved above.
    specialize h₀ (1 / x) (by positivity)
    rw [ge_iff_le, <-sq_le_sq₀ (by positivity) (by positivity), mul_pow] at h₀
    nth_rw 2 [<-Real.rpow_natCast] at h₀
    rw [<-Real.rpow_mul (by positivity), mul_one_div, Real.div_rpow (by positivity) (by positivity), show 1 ^ (3 / 4 * (2 : ℕ) : ℝ) = x ^ (0 : ℝ) by simp, <-Real.rpow_sub (by positivity)] at h₀
    norm_num at h₀
    linarith only [h₀]
  -- Show that 16 * x ^ 3 + 32 * y ^ (-3 / 2) ≥ 48 * (x / y).
  have h₃ (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 16 * x ^ 3 + 32 * y ^ (-3 / 2 : ℝ) ≥ 48 * (x / y) := by
    -- Apply the AM-GM inequality and simplify the expression.
    specialize AM_GM₃ (x ^ 3) (y ^ (-3 / 2 : ℝ)) (y ^ (-3 / 2 : ℝ)) (by positivity) (by positivity) (by positivity)
    nth_rw 2 [<-Real.rpow_natCast] at AM_GM₃
    rw [mul_assoc, <-Real.mul_rpow, <-pow_two] at AM_GM₃
    nth_rw 2 [<-Real.rpow_natCast] at AM_GM₃
    rw [<-Real.rpow_mul, <-Real.rpow_mul, <-Real.rpow_mul] at AM_GM₃
    norm_num at AM_GM₃
    rw [<-neg_div, Real.rpow_neg_one, <-div_eq_mul_inv] at AM_GM₃
    linarith only [AM_GM₃]
    all_goals
      positivity
  -- Show that 16 * x ^ 3 + 32 * y ^ (-3 / 2) = 48 * (x / y) implies x ^ 3 = y ^ (-3 / 2).
  have h₃_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : 16 * x ^ 3 + 32 * y ^ (-3 / 2 : ℝ) = 48 * (x / y)) : x ^ 3 = y ^ (-3 / 2 : ℝ) := by
    -- Apply the equality condition for AM-GM inequality proved above.
    specialize AM_GM₃_eq (x ^ 3) (y ^ (-3 / 2 : ℝ)) (y ^ (-3 / 2 : ℝ)) (by positivity) (by positivity) (by positivity)
    nth_rw 2 [<-Real.rpow_natCast] at AM_GM₃_eq
    rw [mul_assoc, <-Real.mul_rpow, <-pow_two] at AM_GM₃_eq
    nth_rw 2 [<-Real.rpow_natCast] at AM_GM₃_eq
    rw [<-Real.rpow_mul, <-Real.rpow_mul, <-Real.rpow_mul] at AM_GM₃_eq
    norm_num at AM_GM₃_eq h ⊢
    rw [<-AM_GM₃_eq, Real.rpow_neg_one, <-div_eq_mul_inv]
    linarith only [h]
    all_goals
      positivity
  -- We prove partially the inequality, since it is useful in both proving the inequality and the condition for equality.
  have h_ineq : ((3 * a ^ 2 + 1) ^ 2 + 2 * (1 + 3 / b) ^ 2) * ((3 * b ^ 2 + 1) ^ 2 + 2 * (1 + 3 / c) ^ 2) * ((3 * c ^ 2 + 1) ^ 2 + 2 * (1 + 3 / a) ^ 2) ≥ ((16 * a ^ 3) + (32 * b ^ (-3 / 2 : ℝ))) * ((16 * b ^ 3) + (32 * c ^ (-3 / 2 : ℝ))) * ((16 * c ^ 3) + (32 * a ^ (-3 / 2 : ℝ))) := by
    -- Apply the two inequalities h₁ and h₂ to prove the desired result.
    apply mul_le_mul _ _ (by positivity) (by positivity)
    apply mul_le_mul _ _ (by positivity) (by positivity)
    . apply add_le_add
      exact h₁ a ha
      exact h₂ b hb
    . apply add_le_add
      exact h₁ b hb
      exact h₂ c hc
    . apply add_le_add
      exact h₁ c hc
      exact h₂ a ha
  -- Break the goal into separate parts.
  refine ⟨?_, Iff.intro ?_ ?_⟩
  . -- First show that the inequality holds.
    calc
      ((3 * a ^ 2 + 1) ^ 2 + 2 * (1 + 3 / b) ^ 2) * ((3 * b ^ 2 + 1) ^ 2 + 2 * (1 + 3 / c) ^ 2) * ((3 * c ^ 2 + 1) ^ 2 + 2 * (1 + 3 / a) ^ 2)
      _ ≥ ((16 * a ^ 3) + (32 * b ^ (-3 / 2 : ℝ))) * ((16 * b ^ 3) + (32 * c ^ (-3 / 2 : ℝ))) * ((16 * c ^ 3) + (32 * a ^ (-3 / 2 : ℝ))) := by
        exact h_ineq
      _ ≥ (48 * (a / b)) * (48 * (b / c)) * (48 * (c / a)) := by
        -- Apply the inequality h₃.
        apply mul_le_mul _ _ (by positivity) (by positivity)
        apply mul_le_mul _ _ (by positivity) (by positivity)
        . apply h₃ a b ha hb
        . apply h₃ b c hb hc
        . apply h₃ c a hc ha
      _ = 48 ^ 3 := by
        -- Simplify the expression.
        field_simp
        ring
  . -- Next show that if the equality holds, then a = b = c = 1.
    intro h
    -- Show that 16a³ + 32b ^ (-3 / 2) ≤ 48(a / b) and 16b³ + 32c ^ (-3 / 2) ≤ 48(b / c) and 16c³ + 32a ^ (-3 / 2) ≤ 48 (c / a).
    have h' : 16 * a ^ 3 + 32 * b ^ (-3 / 2 : ℝ) ≤ 48 * (a / b) ∧ 16 * b ^ 3 + 32 * c ^ (-3 / 2 : ℝ) ≤ 48 * (b / c) ∧ 16 * c ^ 3 + 32 * a ^ (-3 / 2 : ℝ) ≤ 48 * (c / a) := by
      -- Assume the contrary and derive a contradiction.
      by_contra this
      rw [Classical.not_and_iff_or_not_not, Classical.not_and_iff_or_not_not, not_le, not_le, not_le] at this
      have h_absurd : (48 ^ 3 : ℝ) > 48 ^ 3 := by
        calc
          48 ^ 3 ≥ (16 * a ^ 3 + 32 * b ^ (-3 / 2 : ℝ)) * (16 * b ^ 3 + 32 * c ^ (-3 / 2 : ℝ)) * (16 * c ^ 3 + 32 * a ^ (-3 / 2 : ℝ)) := by
            -- Apply the partial inequality h_ineq and the assumed equality.
            exact (h.symm) ▸ h_ineq
          _ > (48 * (a / b)) * (48 * (b / c)) * (48 * (c / a)) := by
            -- Apply the hypothesis of contrary.
            obtain this | this | this := this
            . rw [mul_assoc, mul_assoc]
              calc
                (16 * a ^ 3 + 32 * b ^ (-3 / 2 : ℝ)) * ((16 * b ^ 3 + 32 * c ^ (-3 / 2 : ℝ)) * (16 * c ^ 3 + 32 * a ^ (-3 / 2 : ℝ)))
                _ > 48 * (a / b) * ((16 * b ^ 3 + 32 * c ^ (-3 / 2 : ℝ)) * (16 * c ^ 3 + 32 * a ^ (-3 / 2 : ℝ))) := by
                  rw [gt_iff_lt, mul_lt_mul_right (by positivity)]
                  exact this
                _ ≥ 48 * (a / b) * ((48 * (b / c)) * (48 * (c / a))) := by
                  rw [ge_iff_le, mul_le_mul_left (by positivity)]
                  apply mul_le_mul _ _ (by positivity) (by positivity)
                  . apply h₃ b c hb hc
                  . apply h₃ c a hc ha
            . rw [mul_comm (16 * a ^ 3 + 32 * b ^ (-3 / 2 : ℝ)), mul_comm (48 * (a / b)), mul_assoc, mul_assoc]
              calc
                (16 * b ^ 3 + 32 * c ^ (-3 / 2 : ℝ)) * ((16 * a ^ 3 + 32 * b ^ (-3 / 2 : ℝ)) * (16 * c ^ 3 + 32 * a ^ (-3 / 2 : ℝ)))
                _ > 48 * (b / c) * ((16 * a ^ 3 + 32 * b ^ (-3 / 2 : ℝ)) * (16 * c ^ 3 + 32 * a ^ (-3 / 2 : ℝ))) := by
                  rw [gt_iff_lt, mul_lt_mul_right (by positivity)]
                  exact this
                _ ≥ 48 * (b / c) * ((48 * (a / b)) * (48 * (c / a))) := by
                  rw [ge_iff_le, mul_le_mul_left (by positivity)]
                  apply mul_le_mul _ _ (by positivity) (by positivity)
                  . apply h₃ a b ha hb
                  . apply h₃ c a hc ha
            . calc
                (16 * a ^ 3 + 32 * b ^ (-3 / 2 : ℝ)) * (16 * b ^ 3 + 32 * c ^ (-3 / 2 : ℝ)) * (16 * c ^ 3 + 32 * a ^ (-3 / 2 : ℝ))
                _ > (16 * a ^ 3 + 32 * b ^ (-3 / 2 : ℝ)) * (16 * b ^ 3 + 32 * c ^ (-3 / 2 : ℝ)) * (48 * (c / a)) := by
                  rw [gt_iff_lt, mul_lt_mul_left (by positivity)]
                  exact this
                _ ≥ 48 * (a / b) * (48 * (b / c)) * (48 * (c / a)) := by
                  rw [ge_iff_le, mul_le_mul_right (by positivity)]
                  apply mul_le_mul _ _ (by positivity) (by positivity)
                  . apply h₃ a b ha hb
                  . apply h₃ b c hb hc
          _ = 48 ^ 3 := by
            -- Simplify the expression.
            field_simp
            ring
      norm_num at h_absurd
    -- Show that 16a³ + 32b ^ (-3 / 2) = 48(a / b) and 16b³ + 32c ^ (-3 / 2) = 48(b / c) and 16c³ + 32a ^ (-3 / 2) = 48 (c / a).
    replace h' : 16 * a ^ 3 + 32 * b ^ (-3 / 2 : ℝ) = 48 * (a / b) ∧ 16 * b ^ 3 + 32 * c ^ (-3 / 2 : ℝ) = 48 * (b / c) ∧ 16 * c ^ 3 + 32 * a ^ (-3 / 2 : ℝ) = 48 * (c / a) := ⟨le_antisymm_iff.mpr ⟨h'.1, ge_iff_le.mp (h₃ a b ha hb)⟩, le_antisymm_iff.mpr ⟨h'.2.1, ge_iff_le.mp (h₃ b c hb hc)⟩, le_antisymm_iff.mpr ⟨h'.2.2, ge_iff_le.mp (h₃ c a hc ha)⟩⟩
    -- Show that a³ = b ^ (-3 / 2), b³ = c ^ (-3 / 2) and c³ = a ^ (-3 / 2).
    replace h' : a ^ 3 = b ^ (-3 / 2 : ℝ) ∧ b ^ 3 = c ^ (-3 / 2 : ℝ) ∧ c ^ 3 = a ^ (-3 / 2 : ℝ) := ⟨h₃_eq a b ha hb h'.1, h₃_eq b c hb hc h'.2.1, h₃_eq c a hc ha h'.2.2⟩
    -- Show that a = 1 combining the three equalities above.
    have ha' : a ^ (12 : ℝ) = a ^ (-3 / 2 : ℝ) := by
      calc
        a ^ (12 : ℝ) = ((a ^ 3) ^ (-2 : ℝ)) ^ (-2 : ℝ) := by
          rw [<-Real.rpow_natCast, <-Real.rpow_mul, <-Real.rpow_mul]
          norm_num
          all_goals
            positivity
        _ = (b ^ 3) ^ (-2 : ℝ) := by
          rw [h'.1, <-Real.rpow_natCast, <-Real.rpow_mul _ (-3 / 2 : ℝ)]
          norm_num
          all_goals
            positivity
        _ = c ^ 3 := by
          rw [h'.2.1, <-Real.rpow_mul, <-Real.rpow_natCast]
          norm_num
          all_goals
            positivity
        _ = a ^ (-3 / 2 : ℝ) := h'.2.2
    replace ha' : a = 1 := by
      -- Assume on the contrary that a ≠ 1 and derive a contradiction using right-injectivity of the real power function.
      by_contra! ha''
      have h_absurd : (12 : ℝ) = -3 / 2 := by
        rcases ha''.lt_or_lt with h | h
        · exact (Real.strictAnti_rpow_of_base_lt_one ha h).injective ha'
        · exact (Real.strictMono_rpow_of_base_gt_one h).injective ha'
      norm_num at h_absurd
    -- Show that b = 1 and c = 1 using the equalities h' and ha'.
    have hb' : b ^ (-3 / 2 : ℝ) = b ^ (0 : ℝ) := by
      rw [ha'] at h'
      exact (h'.1.symm) ▸ (by simp)
    replace hb' : b = 1 := by
      -- Assume on the contrary that b ≠ 1 and derive a contradiction using right-injectivity of the real power function.
      by_contra! hb''
      have h_absurd : (-3 / 2 : ℝ) = 0 := by
        rcases hb''.lt_or_lt with h | h
        · exact (Real.strictAnti_rpow_of_base_lt_one hb h).injective hb'
        · exact (Real.strictMono_rpow_of_base_gt_one h).injective hb'
      norm_num at h_absurd
    have hc' : c ^ (3 : ℝ) = c ^ (0 : ℝ) := by
      rw [ha', Real.one_rpow, <-Real.rpow_natCast c 3] at h'
      exact (h'.2.2) ▸ (by simp)
    replace hc' : c = 1 := by
      -- Assume on the contrary that c ≠ 1 and derive a contradiction using right-injectivity of the real power function.
      by_contra! hc''
      have h_absurd : (3 : ℝ) = 0 := by
        rcases hc''.lt_or_lt with h | h
        · exact (Real.strictAnti_rpow_of_base_lt_one hc h).injective hc'
        · exact (Real.strictMono_rpow_of_base_gt_one h).injective hc'
      norm_num at h_absurd
    -- Show that a = b = c = 1.
    exact ⟨ha' ▸ hb'.symm, hb' ▸ hc'.symm, hc'⟩
  . -- Finally show that a = b = c = 1 gives the equality case.
    rintro ⟨ha', hb', hc'⟩
    subst a
    subst b
    subst c
    norm_num

