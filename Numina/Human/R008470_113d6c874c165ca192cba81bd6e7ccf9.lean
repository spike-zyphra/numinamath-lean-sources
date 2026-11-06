import Mathlib
open Real Polynomial

/- The polynomial $a x^{2}-b x+c$ has two distinct roots $p$ and $q$, with $a, b$,
and $c$ positive integers and with $ 0 < p, q < 1 $. Find the minimum possible value of $a$. -/
theorem algebra_608450: IsLeast { a : ℕ | ∃(b c : ℕ), 0 < a ∧ 0 < b ∧ 0 < c
  ∧ ∃ p q : ℝ, p ≠ q ∧ a * p^2 - b * p + c = 0 ∧ a * q^2 - b * q + c = 0 ∧ 0 < p ∧ p < 1 ∧ 0 < q ∧ q < 1 } 5 := by
  constructor
  · -- First, $a = 5$ is acquirable. We use the numbers $a = 5, b = 5, c = 1$
    simp; use 5; apply And.intro; simp; use 1; apply And.intro; simp; simp;
    let s : ℝ := √ 5
    have hs:  discrim 5 (-5) 1 = s * s := by unfold s discrim; norm_num
    let p : ℝ := (5 + s: ℝ) / (2 * 5: ℝ)
    let q : ℝ := (5 - s: ℝ) / (2 * 5: ℝ)
    use p; use q
    apply And.intro; unfold q p s; ring_nf; norm_num; field_simp
    by_contra! hcx
    have : √ 5 ≠ 0 := by simp
    exact this (by linarith)

    -- Let's check that $p$ and $q$ are indeed the roots we were seeking.
    apply And.intro
    rw [show 5 * p ^ 2 - 5 * p + 1 = 5 * (p * p) + (- 5) * p + 1 by ring]
    apply (quadratic_eq_zero_iff (show (5: ℝ) ≠ 0 by simp) hs p).mpr
    left; unfold p; ring
    apply And.intro
    rw [show 5 * q ^ 2 - 5 * q + 1 = 5 * (q * q) + (- 5) * q + 1 by ring]
    apply (quadratic_eq_zero_iff (show (5: ℝ) ≠ 0 by simp) hs q).mpr
    right; unfold q; ring

    -- Prove also that they are in $(0, 1)$.
    have : √ 5 < 5 := by apply (Real.sqrt_lt' (by simp)).mpr (by linarith)
    apply And.intro; positivity
    apply And.intro; unfold p; norm_num; linarith only [this]
    apply And.intro; unfold q; linarith only [this]
    unfold q; norm_num; linarith only [show √ 5 > 0 by simp]

  · -- Now show that no smaller value of $a$ satisfies the conditions.
    intro a h
    simp at h
    obtain ⟨ha, b, hb, c, hc, p, q, hpq, hp, hq, hpl, hpu, hql, hqu⟩ := h

    have ha_ne0 : (a: ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.not_eq_zero_of_lt ha)
    have hp_copy := hp
    rw [show a * p ^ 2 - b * p + c = a * (p * p) + (- b) * p + c by ring] at hp_copy
    have hq_copy := hq
    rw [show a * q ^ 2 - b * q + c = a * (q * q) + (- b) * q + c by ring] at hq_copy

    set s := √ (discrim (a) (-b) c) with hsdef
    have hs: discrim (↑a) (-↑b) ↑c = s * s := by
      unfold s
      ring_nf
      rw [sq_sqrt]
      rw [(quadratic_eq_zero_iff_discrim_eq_sq (ha_ne0) p).mp hp_copy]
      positivity
    have hs': discrim (↑a) (-↑b) ↑c = s ^ 2 := by rw [hs]; ring

    -- by the basic property for quadratic equations, we know that the root must 
    -- be one of $$ \frac {-b \pm s} {2a},\quad \text{where}\quad b^2-s^2=4ac $$

    have hp_choice := (quadratic_eq_zero_iff ha_ne0 hs p).mp hp_copy
    have hq_choice := (quadratic_eq_zero_iff ha_ne0 hs q).mp hq_copy
    norm_num at hq_choice hp_choice

    -- Without loss of generality, assume $p<q$
    wlog hwlog: p < q
    simp at this hwlog hpq
    specialize this ha b hb c hc q p (Ne.symm hpq) hq hp hql hqu hpl hpu (by linarith [ha_ne0])
      (by linarith only [hq_copy]) (by linarith only [hp_copy])
    apply this
    repeat
      ring_nf
      rw [sq_sqrt]
      rw [(quadratic_eq_zero_iff_discrim_eq_sq (ha_ne0) p).mp hp_copy]
      positivity
    rw [← hsdef]; exact hp_choice
    rw [← hsdef]; exact hq_choice
    apply lt_of_le_of_ne hwlog
    apply Ne.symm
    simp [hpq]


    have hs_nonneg : s ≥ 0 := by unfold s; simp
    -- Since $p < q$ and they are both roots of $a x^{2}-b x+c = 0$, 
    -- then p must be $$\frac {-b - s} {2a}$$ and $q$ must be $$\frac {-b + s} {2a}$$.
    have hpq_val: p = (↑b - s) / (2 * ↑a) ∧ q = (↑b + s) / (2 * ↑a) := by
      cases hp_choice with
      | inl hp_choice1 =>
        cases hq_choice with
        | inl hq_choice1 =>
          by_contra! _
          have : p = q := by linarith
          exact hpq this
        | inr hq_choice2 =>
          by_contra! _
          have : ¬ p < q := by
            simp
            rw [hp_choice1, hq_choice2]
            apply (div_le_div_iff_of_pos_right (by positivity)).mpr
            linarith
          contradiction
      | inr hp_choice2 =>
        cases hq_choice with
        | inl hq_choice1 =>
          exact ⟨hp_choice2, hq_choice1⟩
        | inr hq_choice2 =>
          by_contra! _
          have : p = q := by linarith
          exact hpq this
    obtain ⟨hp_val, hq_val⟩ := hpq_val

    -- Then $p + q = b / a$ and $pq = c / a$
    have hpq_sum : p + q = b / (a: ℝ) := by rw [hp_val, hq_val]; field_simp; linarith
    have hpq_prod : p * q = c / (a: ℝ) := by
      rw [hp_val, hq_val]; ring_nf; rw [← hs']; unfold discrim; field_simp; linarith
    -- As a result, we have $\frac{b}{a}=x+y&lt;2 \Rightarrow b&lt;2 a $
    -- and $\frac{c}{a}=x y&lt;1 \Rightarrow c&lt;a \Rightarrow a&gt;1$
    have : b / (a: ℝ) < 2 := by linarith
    have hb_le_2a: b < 2 * (a: ℝ) := (mul_inv_lt_iff₀ (Nat.cast_pos'.mpr ha)).mp this
    have : p * q < 1 := by
      calc
        p * q < 1 * q := by exact mul_lt_mul_of_pos_right hpu hql
        _ = q := by simp
        _ < 1 := hqu
    have : c / (a: ℝ) < 1 := by linarith
    have hc_rlt_a: c < (a: ℝ) := (div_lt_one (Nat.cast_pos'.mpr ha)).mp this
    have hc_lt_a: c < a := by norm_cast at hc_rlt_a

    -- On the other hand, since $p$ and $q$ are different, then $s$ must be positive, thus $s > 0$
    have hs_pos : s > 0 := by
      apply lt_of_le_of_ne hs_nonneg
      by_contra! hs0
      rw [← hs0] at hp_val hq_val
      simp at hp_val hq_val
      have : p = q := by rw [hp_val, hq_val]
      exact hpq this

    have hdisc_pos : discrim (↑a) (-b:ℝ) ↑c > 0 := by
      apply Real.sqrt_pos.mp
      rw [← hsdef]
      exact hs_pos

    -- We have $s^2 = b^2-4ac>0$ which implies $b > 2c$ by the truth that $a > c$.
    unfold discrim at hdisc_pos
    field_simp at hdisc_pos
    have : (2 * ↑c) ^ 2  < (↑b ^ 2: ℝ) := by
      calc
        _ = (4 * ↑c) * ↑c := by ring
        _ < (4 * ↑c: ℝ) * ↑a := by
          apply mul_lt_mul_of_pos_left hc_rlt_a
          positivity
        _ = (4 * ↑a * ↑c: ℝ) := by ring
        _ < (↑b ^ 2: ℝ) := by exact hdisc_pos
    have h2c_rlt_b : 2 * ↑c  < (↑b: ℝ) := by
      by_contra! hcx
      have : ¬ (2 * ↑c: ℝ) ^ 2 < (↑b ^ 2: ℝ) := by
        simp
        calc
          (2 * ↑c: ℝ) ^ 2
            = (2 * ↑c: ℝ) * (2 * ↑c: ℝ) := by ring
          _ ≥ (2 * ↑c: ℝ) * (↑b: ℝ) := by
            apply mul_le_mul_of_nonneg_left hcx _
            positivity
          _ ≥ (↑b: ℝ) * (↑b: ℝ) := by
            apply mul_le_mul_of_nonneg_right hcx _
            positivity
          _ = (↑b ^ 2: ℝ) := by ring
      contradiction
    have h2c_lt_b: 2 * c < b := by norm_cast at h2c_rlt_b

    -- Evaluated at 1 , the polynomial must be greater than 0.
    have hfx_at_1 : (1 - p) * (1 - q) > 0 := by
      have : 1 - p > 0 := by linarith
      have : 1 - q > 0 := by linarith
      positivity
    rw [hp_val, hq_val] at hfx_at_1
    norm_num at hfx_at_1
    ring_nf at hfx_at_1
    rw [← hs'] at hfx_at_1
    unfold discrim at hfx_at_1
    ring_nf at hfx_at_1
    field_simp at hfx_at_1
    rw [show (↑a - ↑b) * ↑a ^ 2 + ↑a * ↑c * ↑a = (a - b + c: ℝ) * ↑a ^ 2 by ring] at hfx_at_1
    have := (pos_iff_pos_of_mul_pos hfx_at_1).mpr (show (a: ℝ) ^ 2 > 0 by positivity)

    -- so $a+c ≥ b$. 
    have hac_rlt_b : (a + c : ℝ) > b := by linarith
    have hac_lt_b : a + c > b := by norm_cast at hac_rlt_b

    -- then we can get $a ≥ 3$
    have ha_lb : a ≥ 3 := by linarith
    by_contra! hacx
    unfold discrim at hs'
    interval_cases a

    -- Then we discuss on the value of $a$.
    -- If $a = 3$, then $c = 1$ and $b = 3$,
    have hc_val: c = 1 := by linarith
    have hb_val: b = 3 := by linarith
    rw [hc_val] at hac_lt_b h2c_lt_b
    simp at hac_lt_b h2c_lt_b
    rw [hc_val, hb_val] at hs'
    norm_num at hs'
    -- which will leads us to $s ^ 3 = -3$, impossible!
    have : ¬ s ^ 2 ≥ 0 := by linarith
    have : s ^ 2 ≥ 0 := by positivity
    contradiction

    -- If $a = 4$,
    have : 3 > c := by linarith
    interval_cases c
    -- we dicsuss on the value of $c$.
    -- If $a = 4, c = 1$
    simp at hac_lt_b h2c_lt_b
    interval_cases b
    -- If $a = 4, c = 1, b = 3$
    norm_num at hs'
    have : ¬ s ^ 2 ≥ 0 := by linarith
    have : s ^ 2 ≥ 0 := by positivity
    contradiction
    -- If $a = 4, c = 1, b = 4$
    norm_num at hs'
    have : s ^ 2 > 0 := by simp [hs_pos]
    have : ¬ s ^ 2 = 0 := by linarith
    exact this (Eq.symm hs')
    -- If $a = 4, c = 2$
    norm_num at hac_lt_b h2c_lt_b
    have hb_val : b = 5 := by linarith
    rw [hb_val] at hs'
    norm_num at hs'
    have : ¬ s ^ 2 ≥ 0 := by linarith
    have : s ^ 2 ≥ 0 := by positivity
    contradiction
