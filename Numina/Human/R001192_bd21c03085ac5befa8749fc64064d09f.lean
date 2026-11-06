import Mathlib

set_option maxHeartbeats 30000000

open Polynomial

/-Find the number of quadratic equations of the form $x^2 + ax + b = 0,$ such that whenever $c$ is a root of the equation, $c^2 - 2$ is also a root of the equation.-/
theorem algebra_20989 : {(a, b) : ℝ×ℝ | ∃(f : ℂ → ℂ), (∀x : ℂ, f x = x^2 + a * x + b) ∧ ∀c : ℂ, f c = 0 → f (c^2 - 2) = 0}.ncard = 6 := by
  have : {(a, b) : ℝ×ℝ | ∃(f : ℂ → ℂ), (∀x : ℂ, f x = x^2 + a * x + b) ∧ ∀c : ℂ, f c = 0 → f (c^2 - 2) = 0} = {(-4, 4), (2, 1), (-1, -2), (1, -1), (0, -4), (0, -1)} := by
    ext ⟨a, b⟩
    simp
    constructor
    · intro ⟨f, hf₁, hf₂⟩
      have exist_root : ∃r : ℂ, f r = 0 := by
        use ((a^2 - 4 * b)^(1/2 : ℂ) - a)/2
        rw [hf₁]
        ring_nf
        rw [←Complex.cpow_mul_nat]
        simp
        ring_nf
      obtain ⟨c, hc₁⟩ := exist_root
      have hc₂ := hf₂ c hc₁

      have discrim_eq_zero_of_existsUnique {a b c : ℂ} (ha : a ≠ 0) : (∃! x, a * (x * x) + b * x + c = 0) → discrim a b c = 0 := by
        simp_rw [quadratic_eq_zero_iff_discrim_eq_sq ha]
        generalize discrim a b c = d
        rintro ⟨x, rfl, hx⟩
        specialize hx (-(x + b / a))
        field_simp [ha] at hx
        specialize hx (by ring)
        linear_combination -(2 * a * x + b) * hx

      by_cases one_root : ∃!r : ℂ, f r = 0
      · -- If $c$ is the only root
        have h_discrim : discrim (1 : ℂ) a b = 0 := by
          apply discrim_eq_zero_of_existsUnique
          simp
          simp [←pow_two]
          simp_rw [hf₁] at one_root
          exact one_root
        rw [discrim] at h_discrim

        have : c = c^2 - 2 := by
          rcases one_root with ⟨r, hr₁, hr₂⟩
          simp at hr₂
          have h₁ := hr₂ c hc₁
          have h₂ := hr₂ (c^2 - 2) hc₂
          rw [h₂, h₁]
        have : (c - 2) * (c + 1) = 0 := by linear_combination -this
        simp at this
        rw [hf₁] at hc₂ hc₁
        obtain (hc | hc) := this
        · -- c = 2
          have : c = 2 := by linear_combination hc
          rw [this] at hc₂
          norm_cast at hc₂ h_discrim
          norm_num at hc₂ h_discrim
          have ha : a = -4 := by
            have : (a + 4)^2 = 0 := by linarith
            simp at this
            linarith
          have hb : b = 4 := by linarith
          rw [ha, hb]
          simp
        · -- c = -1
          have : c = -1 := by linear_combination hc
          rw [this] at hc₂
          norm_cast at hc₂ h_discrim
          norm_num at hc₂ h_discrim
          have ha : a = 2 := by
            have : (a - 2)^2 = 0 := by linarith
            simp at this
            linarith
          have hb : b = 1 := by linarith
          rw [ha, hb]
          simp

      -- Then, x^2 + a * x + b = 0 have two roots.
      -- so, (x - c) * (x - r) = x^2 - (c + r) * x + c * r = 0
      -- and, r is the different root from c
      have : ∃r, r ≠ c ∧ f r = 0 := by
        by_contra!
        have : ∃!r, f r = 0 := by
          use c
          simp
          use hc₁
          intro r hr₁
          by_contra! hr₂
          specialize this r hr₂
          exact absurd hr₁ this
        exact one_root this
      obtain ⟨r, hr₀, hr₁⟩ := this
      have hr₂ := hf₂ r hr₁

      -- So, {c, r} = (X^2 + a * X + b).roots
      obtain ⟨P, hP⟩ := show ∃P, P = (X^2 + (C a : ℂ[X]) * X + (C b : ℂ[X]) : ℂ[X]) by simp
      obtain ⟨roots, h_roots⟩ := show ∃(r': Multiset ℂ), r' = {c, r} by simp
      have p_degree : P.natDegree = 2 := by rw [hP]; compute_degree!
      have p_ne_zero : P ≠ 0 := by
        apply leadingCoeff_ne_zero.mp
        have : P.Monic := by
          apply Monic.def.mpr
          rw [coeff_natDegree.symm, p_degree, hP]
          simp
        rw [this]
        simp
      have h_roots' : P.roots = roots := by
        have card_le : Multiset.card P.roots ≤ Multiset.card roots := by
          rw [h_roots]
          simp
          apply le_trans P.card_roots'
          apply Nat.le_of_eq p_degree
        have p_monic : P.Monic := by
          apply Monic.def.mpr
          rw [coeff_natDegree.symm, p_degree, hP]
          simp
        have p_ne_zero : P ≠ 0 := by
          apply leadingCoeff_ne_zero.mp
          rw [p_monic]
          simp
        have roots_is_subset : roots ⊆ P.roots := by
          rw [h_roots]
          simp
          rw [hf₁] at hc₁ hr₁
          refine ⟨⟨p_ne_zero, ?_⟩, ⟨p_ne_zero, ?_⟩⟩
          repeat rw [hP]; simp; assumption
        refine Eq.symm (Multiset.eq_of_le_of_card_le ?_ card_le)
        have nodup_r : roots.Nodup := by rw [h_roots]; simp; exact Ne.symm hr₀
        exact (Multiset.le_iff_subset nodup_r).mpr roots_is_subset
      have h₁ : c^2 - 2 = c ∨ c^2 - 2 = r := by
        have : c^2 - 2 ∈ P.roots := by
          apply mem_roots'.mpr
          refine ⟨p_ne_zero, ?_⟩
          rw [hP]
          simp
          rw [←hf₁]
          assumption
        rw [h_roots', h_roots] at this
        simp at this
        assumption
      have h₂ : r^2 - 2 = c ∨ r^2 - 2 = r := by
        have : r^2 - 2 ∈ P.roots := by
          apply mem_roots'.mpr
          refine ⟨p_ne_zero, ?_⟩
          rw [hP]
          simp
          rw [←hf₁]
          assumption
        rw [h_roots', h_roots] at this
        simp at this
        assumption
      obtain (h₁ | h₁) := h₁
      · -- c^2 - 2 = c
        -- so, we have (c + 1) * (c - 2) = 0
        have : (c + 1) * (c - 2) = 0 := by linear_combination h₁
        simp at this
        obtain (h₂ | h₂) := h₂
        · -- r^2 - 2 = c, so, r^2 - 2 = c^2 - 2
          have eq₁ : r^2 = c^2 := by linear_combination h₂ - h₁
          -- so, -r = c
          rw [show r = r.re + Complex.I * r.im by apply Complex.ext; repeat simp] at eq₁
          rw [show c = c.re + Complex.I * c.im by apply Complex.ext; repeat simp] at eq₁
          rw [Complex.ext_iff] at eq₁
          ring_nf at eq₁
          simp at eq₁
          norm_cast at eq₁
          simp at eq₁
          have : r.re = c.re ∧ r.im = c.im ∨ r.re = -c.re ∧ r.im = -c.im := by
            obtain ⟨eq₁, eq₂⟩ := eq₁
            by_cases h₁ : r.re = 0
            · -- if r.re = 0
              rw [h₁] at eq₁ eq₂
              simp at eq₁ eq₂
              obtain (h₂ | h₂) := eq₂
              · -- c.re = 0
                rw [h₂] at eq₁
                simp at eq₁
                rw [h₁, h₂]
                simp
                rw [sq_eq_sq_iff_abs_eq_abs, abs_eq_abs] at eq₁
                assumption
              · -- c.im = 0
                rw [h₂] at eq₁
                simp at eq₁
                rw [h₁, h₂]
                have ineq₁ : -r.im^2 ≤ 0 := by linarith [sq_nonneg r.im]
                have ineq₂ : 0 ≤ -r.im^2 := by rw [eq₁]; linarith [sq_nonneg c.re]
                have : r.im^2 = 0 := by linarith [ineq₁, ineq₂]
                simp at this
                rw [this, Eq.comm] at eq₁
                simp at eq₁
                rw [this, eq₁]
                simp
            -- if r.re ≠ 0, we get r.im = c.re * c.im / r.re
            rw [CancelDenoms.cancel_factors_eq_div eq₂ h₁] at eq₁
            have eq₁ : (r.re^2 + c.im^2) * (r.re^2 - c.re^2) = 0 := by
              have : r.re^2 * (r.re ^ 2 + -(c.re * c.im / r.re) ^ 2) = r.re ^ 2 * (-c.im ^ 2 + c.re ^ 2) := by rw [eq₁]
              ring_nf at this
              rw [mul_comm _ (r.re⁻¹ ^ 2), ←mul_assoc, ←mul_assoc] at this
              have h : r.re⁻¹ ^ 2 * r.re ^ 2 = 1 := by
                rw [←mul_pow, mul_comm, ←one_div, mul_div, mul_one, div_self h₁]
                simp
              rw [h] at this
              simp at this
              linear_combination this
            simp at eq₁
            obtain (h₂ | h₂) := eq₁
            · -- r.re^2 + c.im^2 = 0
              -- so, r.re = 0, which is a contradiction
              have ineq₁ : -r.re^2 ≤ 0 := by linarith [sq_nonneg r.re]
              have eq₁ : r.re^2 = -c.im^2 := by linear_combination h₂
              have ineq₂ : 0 ≤ -r.re^2 := by rw [eq₁]; linarith [sq_nonneg c.im]
              have : r.re^2 = 0 := by linarith [ineq₁, ineq₂]
              simp at this
              exact absurd this h₁
            · -- r.re^2 - c.re^2 = 0
              -- have h₃: (r.im - c.im) * (r.im + c.im) = 0 := by linarith
              have h₃: (r.re + c.re) * (r.re - c.re) = 0 := by linear_combination h₂
              simp at h₃
              obtain (h₃ | h₃) := h₃
              · -- r.re + c.re = 0
                have : c.re = -r.re := by linear_combination h₃
                rw [this, neg_mul_comm, mul_right_inj' (by assumption)] at eq₂
                rw [this, eq₂]
                simp
              · -- r.re - c.re = 0
                have : c.re = r.re := by linear_combination -h₃
                rw [this, mul_right_inj' (by assumption)] at eq₂
                rw [this, eq₂]
                simp
          rw [←Complex.ext_iff] at this
          obtain (h | h) := this
          · -- r = c
            exact absurd h hr₀
          · -- r.re = -c.re, r.im = -c.im
            have eq₁ : r = -c := by
              apply Complex.ext <;> simp <;> linarith
            obtain (hc₀ | hc₀) := this
            · -- c = -1
              have hc₀ : c = -1 := by linear_combination hc₀
              have hr₀ : r = 1 := by linear_combination eq₁-hc₀
              rw [hf₁] at hr₁ hc₁
              rw [hc₀] at hc₁
              rw [hr₀] at hr₁
              norm_cast at hr₁ hc₁
              simp at hr₁ hc₁
              rw [show a = 0 by linarith, show b = -1 by linarith]
              simp
            · -- c = 2
              have hc₀ : c = 2 := by linear_combination hc₀
              have hr₀ : r = -2 := by linear_combination eq₁-hc₀
              rw [hf₁] at hr₁ hc₁
              rw [hc₀] at hc₁
              rw [hr₀] at hr₁
              norm_cast at hr₁ hc₁
              simp at hr₁ hc₁
              rw [show a = 0 by linarith, show b = -4 by linarith]
              simp
        · -- r^2 - 2 = r
          -- so, r = -1 or 2
          have : (r + 1) * (r - 2) = 0 := by linear_combination h₂
          simp at this
          obtain (hr₃ | hr₃) := this
          · -- r + 1 = 0
            obtain (hc₀ | hc₀) := this
            · -- c + 1 = 0 ∧ r + 1 = 0, so, r = c
              have : r = c := by linear_combination hr₃ - hc₀
              exact absurd this hr₀
            · -- c - 2 = 0 ∧ r + 1 = 0
              have : c = 2 := by linear_combination hc₀
              rw [this] at hc₁
              have : r = -1 := by linear_combination hr₃
              rw [this] at hr₁
              rw [hf₁] at hr₁ hc₁
              norm_cast at hr₁ hc₁
              simp at hr₁ hc₁
              rw [show a = -1 by linarith, show b = -2 by linarith]
              simp
          · -- r - 2 = 0
            obtain (hc₀ | hc₀) := this
            · -- c + 1 = 0 ∧ r - 2 = 0
              have : c = -1 := by linear_combination hc₀
              rw [this] at hc₁
              have : r = 2 := by linear_combination hr₃
              rw [this] at hr₁
              rw [hf₁] at hr₁ hc₁
              norm_cast at hr₁ hc₁
              simp at hr₁ hc₁
              rw [show a = -1 by linarith, show b = -2 by linarith]
              simp
            · -- c - 2 = 0 ∧ r - 2 = 0, so r = c
              have : r = c := by linear_combination hr₃ - hc₀
              exact absurd this hr₀
      · -- c^2 - 2 = r
        have P_eq_mul : P = (X - C c) * (X - C r) := by
          have : Splits (RingHom.id ℂ) P := by
            apply splits_iff_card_roots.mpr
            rw [h_roots', h_roots, p_degree]
            simp
          have := Polynomial.eq_prod_roots_of_splits this
          simp at this
          rw [h_roots', h_roots] at this
          simp at this
          have p_monic : P.Monic := by
            apply Monic.def.mpr
            rw [coeff_natDegree.symm, p_degree, hP]
            simp
          rw [this, p_monic]
          simp
        have sq_sqrt_5 : (√5 : ℂ) ^ 2 = 5 := by
              norm_cast
              rw [Real.sq_sqrt (by linarith)]
        have ϕ_f : ∀ (x : ℂ), (x - (√5 - 1) / 2) * (x + (√5 + 1) / 2) = x^2 + x - 1 := by
          intro x
          ring_nf
          rw [sq_sqrt_5]
          ring_nf
        have hf₃ : ∀x, f x = (x - c) * (x - r) := by
          intro x
          have : ((X - C c) * (X - C r)).eval x = (X^2 + (C a : ℂ[X]) * X + (C b : ℂ[X]) : ℂ[X]).eval x := by rw [←P_eq_mul, hP]
          simp at this
          rw [this]
          exact hf₁ x
        obtain (h₂ | h₂) := h₂
        · -- r ^ 2 - 2 = c
          rw [h₂.symm] at h₁
          have : (r - 2) * (r + 1) * (r - (√5 - 1) / 2) * (r + (√5 + 1) / 2) = 0 := by
            ring_nf
            rw [sq_sqrt_5]
            linear_combination h₁
          simp at this
          obtain (((hr₃ | hr₃) | hr₃) | hr₃) := this
          · -- r - 2 = 0
            have : r = 2 := by linear_combination hr₃
            rw [this] at hr₁ h₂
            have : r = c := by linear_combination this + h₂
            exact absurd this hr₀
          · -- r + 1 = 0
            have : r = -1 := by linear_combination hr₃
            rw [this] at hr₁ h₂
            have : r = c := by linear_combination this + h₂
            exact absurd this hr₀
          · -- r - (√5 - 1) / 2 = 0
            have hr₀ : r = (√5 - 1) / 2 := by linear_combination hr₃
            rw [hr₀] at hr₁ h₂
            have hc₀ : c = -(√5 + 1) / 2 := by
              ring_nf at h₂
              rw [sq_sqrt_5] at h₂
              linear_combination -h₂
            rw [hc₀, hr₀, neg_div] at hf₃
            have hb := hf₃ 0
            rw [sub_neg_eq_add, mul_comm, ϕ_f 0, hf₁ 0] at hb
            norm_cast at hb
            simp at hb
            have ha := hf₃ 1
            rw [sub_neg_eq_add, mul_comm, ϕ_f 1, hf₁ 1, hb] at ha
            norm_cast at ha
            simp at ha
            rw [ha, hb]
            norm_num
          · -- r + (√5 + 1) / 2 = 0
            have hr₀ : r = -(√5 + 1) / 2 := by linear_combination hr₃
            rw [hr₀] at hr₁ h₂
            have hc₀ : c = (√5 - 1) / 2 := by
              ring_nf at h₂
              rw [sq_sqrt_5] at h₂
              linear_combination -h₂
            rw [hc₀, hr₀, neg_div] at hf₃
            have hb := hf₃ 0
            rw [sub_neg_eq_add, ϕ_f 0, hf₁ 0] at hb
            norm_cast at hb
            simp at hb
            have ha := hf₃ 1
            rw [sub_neg_eq_add, ϕ_f 1, hf₁ 1, hb] at ha
            norm_cast at ha
            simp at ha
            rw [ha, hb]
            norm_num
        · -- r^2 - 2 = r = c^2 - 1, so, c = -r
          have eq₁ : r^2 = c^2 := by linear_combination h₂ - h₁
          -- so, -r = c
          rw [show r = r.re + Complex.I * r.im by apply Complex.ext; repeat simp] at eq₁
          rw [show c = c.re + Complex.I * c.im by apply Complex.ext; repeat simp] at eq₁
          rw [Complex.ext_iff] at eq₁
          ring_nf at eq₁
          simp at eq₁
          norm_cast at eq₁
          simp at eq₁
          have : r.re = c.re ∧ r.im = c.im ∨ r.re = -c.re ∧ r.im = -c.im := by
            obtain ⟨eq₁, eq₂⟩ := eq₁
            by_cases h₁ : r.re = 0
            · -- if r.re = 0
              rw [h₁] at eq₁ eq₂
              simp at eq₁ eq₂
              obtain (h₂ | h₂) := eq₂
              · -- c.re = 0
                rw [h₂] at eq₁
                simp at eq₁
                rw [h₁, h₂]
                simp
                rw [sq_eq_sq_iff_abs_eq_abs, abs_eq_abs] at eq₁
                assumption
              · -- c.im = 0
                rw [h₂] at eq₁
                simp at eq₁
                rw [h₁, h₂]
                have ineq₁ : -r.im^2 ≤ 0 := by linarith [sq_nonneg r.im]
                have ineq₂ : 0 ≤ -r.im^2 := by rw [eq₁]; linarith [sq_nonneg c.re]
                have : r.im^2 = 0 := by linarith [ineq₁, ineq₂]
                simp at this
                rw [this, Eq.comm] at eq₁
                simp at eq₁
                rw [this, eq₁]
                simp
            -- if r.re ≠ 0, we get r.im = c.re * c.im / r.re
            rw [CancelDenoms.cancel_factors_eq_div eq₂ h₁] at eq₁
            have eq₁ : (r.re^2 + c.im^2) * (r.re^2 - c.re^2) = 0 := by
              have : r.re^2 * (r.re ^ 2 + -(c.re * c.im / r.re) ^ 2) = r.re ^ 2 * (-c.im ^ 2 + c.re ^ 2) := by rw [eq₁]
              ring_nf at this
              rw [mul_comm _ (r.re⁻¹ ^ 2), ←mul_assoc, ←mul_assoc] at this
              have h : r.re⁻¹ ^ 2 * r.re ^ 2 = 1 := by
                rw [←mul_pow, mul_comm, ←one_div, mul_div, mul_one, div_self h₁]
                simp
              rw [h] at this
              simp at this
              linear_combination this
            simp at eq₁
            obtain (h₂ | h₂) := eq₁
            · -- r.re^2 + c.im^2 = 0
              -- so, r.re = 0, which is a contradiction
              have ineq₁ : -r.re^2 ≤ 0 := by linarith [sq_nonneg r.re]
              have eq₁ : r.re^2 = -c.im^2 := by linear_combination h₂
              have ineq₂ : 0 ≤ -r.re^2 := by rw [eq₁]; linarith [sq_nonneg c.im]
              have : r.re^2 = 0 := by linarith [ineq₁, ineq₂]
              simp at this
              exact absurd this h₁
            · -- r.re^2 - c.re^2 = 0
              -- have h₃: (r.im - c.im) * (r.im + c.im) = 0 := by linarith
              have h₃: (r.re + c.re) * (r.re - c.re) = 0 := by linear_combination h₂
              simp at h₃
              obtain (h₃ | h₃) := h₃
              · -- r.re + c.re = 0
                have : c.re = -r.re := by linear_combination h₃
                rw [this, neg_mul_comm, mul_right_inj' (by assumption)] at eq₂
                rw [this, eq₂]
                simp
              · -- r.re - c.re = 0
                have : c.re = r.re := by linear_combination -h₃
                rw [this, mul_right_inj' (by assumption)] at eq₂
                rw [this, eq₂]
                simp
          rw [←Complex.ext_iff] at this
          obtain (h | h) := this
          · -- r = c
            exact absurd h hr₀
          · -- r.re = -c.re, r.im = -c.im
            have eq₁ : r = -c := by
              apply Complex.ext <;> simp <;> linarith
            have : (r + 1) * (r - 2) = 0 := by linear_combination h₂
            simp at this
            obtain (hr₀ | hr₀) := this
            · -- r = -1
              have hr₀ : r = -1 := by linear_combination hr₀
              have hc₀ : c = 1 := by linear_combination eq₁-hr₀
              rw [hf₁] at hr₁ hc₁
              rw [hc₀] at hc₁
              rw [hr₀] at hr₁
              norm_cast at hr₁ hc₁
              simp at hr₁ hc₁
              rw [show a = 0 by linarith, show b = -1 by linarith]
              simp
            · -- r = 2
              have hr₀ : r = 2 := by linear_combination hr₀
              have hc₀ : c = -2 := by linear_combination eq₁-hr₀
              rw [hf₁] at hr₁ hc₁
              rw [hc₀] at hc₁
              rw [hr₀] at hr₁
              norm_cast at hr₁ hc₁
              simp at hr₁ hc₁
              rw [show a = 0 by linarith, show b = -4 by linarith]
              simp
    · -- Prove that, when (a, b) ∈ {(-4, 4), (2, 1), (-1, -2), (1, -1), (0, -4), (0, -1)}
      -- c is a root of the equation, c^2 - 2 is also a root of the equation.
      rintro (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩)
      all_goals
        use (λx ↦ x^2 + a * x + b : ℂ → ℂ)
        simp
        rw [ha, hb]
        simp
        intro c hc
      · -- c^2 - 4c + 4 = 0
        rw [show c^2 - 2 = 4 * c - 6 by linear_combination hc]
        ring_nf
        linear_combination hc * 16
      · -- c^2 + 2c + 1 = 0
        rw [show c^2 - 2 = -2 * c - 3 by linear_combination hc]
        ring_nf
        linear_combination hc * 4
      · -- c^2 - c - 2 = 0
        rw [show c^2 - 2 = c by linear_combination hc]
        ring_nf
      · -- c^2 + c - 1 = 0
        rw [show c^2 - 2 = -c - 1 by linear_combination hc]
        ring_nf
        linear_combination hc
      · -- c^2 - 4 = 0
        rw [show c^2 - 2 = 2 by linear_combination hc]
        ring_nf
      · -- c^2 - 1 = 0
        rw [show c^2 - 2 = -1 by linear_combination hc]
        ring_nf
  rw [this]
  norm_num
