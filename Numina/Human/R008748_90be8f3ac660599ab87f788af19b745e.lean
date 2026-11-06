import Mathlib

open Real


/- Find all triples of positive real numbers $(a, b, c)$ so that the expression

$$
M=\frac{(a+b)(b+c)(a+b+c)}{a b c}
$$

gets its least value. -/
theorem inequalities_606230 (hM : M = fun (a, b, c) => (a + b) * (b + c) * (a + b + c) / (a * b * c))
    (hD : D = {(a, b, c) : ℝ × ℝ × ℝ | a > 0 ∧ b > 0 ∧ c > 0}):
    {(a, b, c) : ℝ × ℝ × ℝ | (a, b, c) ∈ D ∧ IsMinOn M D (a, b, c)} =
    {(t * ((1 + √5) / 2) ^ (1 / (3 : ℝ)), t * ((3 - √5) / 2) ^ (1 / (3 : ℝ)), t * ((1 + √5) / 2) ^ (1 / (3 : ℝ))) | t > 0} := by
  -- prove some properties
  have hphi1 : goldenRatio ≥ 0 := by exact le_of_lt gold_pos
  have hphi2 : goldenRatio ^ 2 = (3 + √ 5) / 2 := by
    simp [gold_sq]
    ring
  have hphi3 : 1 / goldenRatio ^ 2 = (3 - √ 5) / 2 := by
    rw [hphi2]
    field_simp
    ring_nf
    simp
    ring
  have hphi4 {a : ℝ} : 0 ≤ goldenRatio ^ a := by exact rpow_nonneg hphi1 a

  -- assume a * b * c = 1
  have hMax (hM : M = fun (a, b, c) => (a + b) * (b + c) * (a + b + c) / (a * b * c))
      (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hmul : a * b * c = 1) :
      M (a, b, c) ≥ (11 + 5 * √5) / 2 ∧
      (M (a, b, c) = (11 + 5 * √5) / 2 ↔ a = ((1 + √5) / 2) ^ (1 / (3 : ℝ)) ∧ c = ((1 + √5) / 2) ^ (1 / (3 : ℝ)) ∧ b = ((3 - √5) / 2) ^ (1 / (3 : ℝ))) := by
    -- We set $s=a+c$ and $p=a c$ and using $b=\frac{1}{a c}$, we get
    -- $$ M=\left(a+\frac{1}{a c}\right)\left(\frac{1}{a c}+c\right)\left(a+\frac{1}{a c}+c\right)=\left(a+p^{-1}\right)\left(c+p^{-1}\right)\left(s+p^{-1}\right) $$
    let s := a + c
    let p := a * c
    have hppos : p > 0 := by exact mul_pos ha hc
    have hp : p ≥ 0 := by exact le_of_lt hppos
    have hpne : p ≠ 0 := by exact ne_of_gt hppos
    have hb1 : b = 1 / p := by
        simp [p, ←hmul]
        field_simp
        ring
    -- Expanding the right-hand side we get
    -- $$ M=p s+\frac{s^{2}}{p}+1+\frac{2 s}{p^{2}}+\frac{1}{p^{3}} $$
    have hM : M (a, b, c) = p * s + s ^ 2 / p + 1 + 2 * s / p ^ 2 + 1 / p ^ 3 := by
      simp only [hM, hmul, div_one]
      calc
        _ = (a + 1 / p) * (c + 1 / p) * (s + 1 / p) := by
          rw [hb1]
          congr 1
          · congr 1
            rw [add_comm]
          · ring
        _ = (p + s / p + 1 / p ^ 2) * (s + 1 / p) := by
          congr 1
          ring
        _ = _ := by
          have (p s : ℝ) (hp : p ≠ 0) : (p + s / p + 1 / p ^ 2) * (s + 1 / p) = p * s + s ^ 2 / p + 1 + 2 * s / p ^ 2 + 1 / p ^ 3 := by
            ring_nf
            rw [mul_inv_cancel₀ hp]
            ring
          rw [this]
          exact hpne

    suffices hstep1 : p * s + s ^ 2 / p + 1 + 2 * s / p ^ 2 + 1 / p ^ 3 ≥ (11 + 5 * √5) / 2 ∧
        (p * s + s ^ 2 / p + 1 + 2 * s / p ^ 2 + 1 / p ^ 3 = (11 + 5 * √5) / 2 ↔ p = (goldenRatio) ^ (2 / (3 : ℝ)) ∧ a = c)
    · -- rewrite the result
      rw [←hM] at hstep1
      constructor
      · exact hstep1.1
      · constructor <;> intro h
        · apply hstep1.2.mp at h
          obtain hp := h.1
          simp [p] at h
          obtain ⟨h1, h2⟩ := h
          rw [h2, ←sq, eq_comm] at h1
          apply sqrt_eq_iff_eq_sq hphi4 (le_of_lt hc) |>.mpr at h1
          rw [sqrt_eq_rpow, ←rpow_mul hphi1] at h1
          norm_num at h1
          rw [h2, hb1, h1, ←hphi3, div_rpow (by norm_num) (by apply sq_nonneg), hp, ←rpow_natCast, ←rpow_mul hphi1]
          simp
          norm_num
        · apply hstep1.2.mpr
          simp [p, h.1, h.2.1]
          rw [←mul_rpow hphi1 hphi1, ←sq, ←rpow_natCast, ←rpow_mul hphi1]
          norm_num
    · -- Now by $s \geq 2 \sqrt{p}$ and setting $x=p \sqrt{p}&gt;0$
      have hsp : s ≥ 2 * √ p ∧
          (s = 2 * √ p ↔ a = c) := by
        have : s = (√a - √c) ^ 2 + 2 * √p := by
          ring_nf
          rw [sq_sqrt (le_of_lt ha), sq_sqrt (le_of_lt hc), sqrt_mul (le_of_lt ha)]
          ring
        simp [this]
        constructor
        · apply sq_nonneg
        · constructor <;> intro h
          · apply sub_eq_zero.mp at h
            rw [←sq_sqrt (le_of_lt ha), ←sq_sqrt (le_of_lt hc)]
            congr
          · simp [h]
      let x := p * √ p
      have hx : x > 0 := by
        simp [x]
        apply mul_pos hppos
        apply sqrt_pos.mpr hppos
      -- we get $$ M \geq 2 x+5+\frac{4}{x}+\frac{1}{x^{2}} $$
      have hM : p * s + s ^ 2 / p + 1 + 2 * s / p ^ 2 + 1 / p ^ 3 ≥ 2 * x + 5 + 4 / x + 1 / x ^ 2 ∧
          (p * s + s ^ 2 / p + 1 + 2 * s / p ^ 2 + 1 / p ^ 3 = 2 * x + 5 + 4 / x + 1 / x ^ 2 ↔ a = c):= by
        have h1 : p * s + s ^ 2 / p + 1 + 2 * s / p ^ 2 + 1 / p ^ 3 ≥ p * (2 * √ p) + (2 * √ p) ^ 2 / p + 1 + 2 * (2 * √ p) / p ^ 2 + (p ^ 3)⁻¹ ∧
            (p * s + s ^ 2 / p + 1 + 2 * s / p ^ 2 + 1 / p ^ 3 = p * (2 * √ p) + (2 * √ p) ^ 2 / p + 1 + 2 * (2 * √ p) / p ^ 2 + (p ^ 3)⁻¹ ↔ s = 2 * √ p) := by
          constructor
          · simp
            rel [hsp.1]
          · constructor <;> intro h
            · have : (p + (s + 2 * √ p) / p + 2 / p ^ 2) * (s - 2 * √ p) = 0 := by
                calc
                  _ = (p * s + s ^ 2 / p + 1 + 2 * s / p ^ 2 + 1 / p ^ 3) - (p * (2 * √ p) + (2 * √ p) ^ 2 / p + 1 + 2 * (2 * √ p) / p ^ 2 + (p ^ 3)⁻¹) := by ring_nf
                  _ = 0 := by rw [h]; ring
              simp at this
              rcases this with h | h
              · have : ¬ p + (s + 2 * √p) / p + 2 / p ^ 2 = 0 := by
                  apply ne_of_gt
                  apply add_pos
                  · apply add_pos hppos
                    apply div_pos ?_ hppos
                    apply add_pos
                    · simp [s]
                      exact add_pos ha hc
                    · apply mul_pos (by norm_num)
                      exact sqrt_pos_of_pos hppos
                  · apply div_pos (by norm_num)
                    apply sq_pos_of_pos hppos
                contradiction
              · exact sub_eq_zero.mp h
            · simp [h]
        have h2 : p * (2 * √ p) + (2 * √ p) ^ 2 / p + 1 + 2 * (2 * √ p) / p ^ 2 + (p ^ 3)⁻¹ = 2 * x + 5 + 4 / x + 1 / x ^ 2 := by
          simp [x, mul_pow, sq_sqrt hp, mul_div_cancel_right₀ _ hpne]
          congr 1
          · congr 1
            · ring
            · field_simp
              ring_nf
              rw [sq_sqrt hp]
              ring
          · field_simp
            ring
        constructor
        · calc
            _ ≥ p * (2 * √ p) + (2 * √ p) ^ 2 / p + 1 + 2 * (2 * √ p) / p ^ 2 + (p ^ 3)⁻¹ := by exact h1.1
            _ = _ := by exact h2
        · constructor <;> intro h
          · apply hsp.2.mp
            apply h1.2.mp
            rw [h, h2]
          · apply hsp.2.mpr at h
            apply h1.2.mpr at h
            rw [h, h2]
      suffices hstep2 : 2 * x + 5 + 4 / x + 1 / x ^ 2 ≥ (11 + 5 * √5) / 2 ∧
          (2 * x + 5 + 4 / x + 1 / x ^ 2 = (11 + 5 * √5) / 2 ↔ x = goldenRatio)
      · -- again rewrite the result
        constructor
        · apply le_trans ?_ hM.1
          exact hstep2.1
        · constructor <;> intro h
          · rw [h] at hM
            have hx : 2 * x + 5 + 4 / x + 1 / x ^ 2 = (11 + 5 * √5) / 2 := by exact le_antisymm hM.1 hstep2.1
            obtain hx' := hstep2.2.mp hx
            constructor
            · rw [←hx']
              simp [x]
              rw [sqrt_eq_rpow , ←rpow_one_add' hp (by norm_num), ←rpow_mul hp]
              norm_num
            · apply hM.2.mp
              exact id (Eq.symm hx)
          · have : x = goldenRatio ∧ a = c := by
              simp [x, h.2, h.1]
              rw [sqrt_eq_rpow, ←rpow_mul hphi1, ←rpow_add gold_pos]
              norm_num
            obtain h := hM.2.mpr this.2
            obtain h' := hstep2.2.mpr this.1
            rw [h, h']
      · -- We will now prove that $$ 2 x+5+\frac{4}{x}+\frac{1}{x^{2}} \geq \frac{11+5 \sqrt{5}}{2} \text {. } $$
        suffices hstep3 : 4 * x ^ 3 - (5 * √5 + 1) * x ^ 2 + 8 * x + 2 ≥ 0 ∧
          (4 * x ^ 3 - (5 * √5 + 1) * x ^ 2 + 8 * x + 2 = 0 ↔ x = goldenRatio)
        · -- Indeed, the latter is equivalent to $4 x^{3}-(5 \sqrt{5}+1) x^{2}+8 x+2 \geq 0$,
          have htrans : 2 * x + 5 + 4 / x + 1 / x ^ 2 = (11 + 5 * √5) / 2 + (4 * x ^ 3 - (5 * √5 + 1) * x ^ 2 + 8 * x + 2) / (2 * x ^ 2) := by
            field_simp
            ring
          rw [htrans]
          simp
          constructor
          · apply div_nonneg
            · exact hstep3.1
            · apply mul_nonneg (by norm_num)
              apply sq_nonneg
          · constructor <;> intro h
            · apply hstep3.2.mp
              simp [show x ≠ 0 by apply ne_of_gt hx] at h
              exact h
            · apply Or.inl
              exact hstep3.2.mpr h
        · -- which can be rewritten as $$ \left(x-\frac{1+\sqrt{5}}{2}\right)^{2}(4 x+3-\sqrt{5}) \geq 0 $$, which is true.
          have heq {x : ℝ} : (x - (1 + √5) / 2) ^ 2 * (4 * x + (3 - √ 5)) = 4 * x ^ 3 - (5 * √5 + 1) * x ^ 2 + 8 * x + 2 := by
            field_simp
            ring_nf
            have : √5 ^ 3 = 5 * √ 5 := by
              rw [pow_succ]
              norm_num
            rw [this]
            simp
            ring
          rw [←heq]
          constructor
          · apply mul_nonneg
            · apply sq_nonneg
            · apply add_nonneg
              · linarith
              · simp
                apply sqrt_le_iff.mpr
                norm_num
          · constructor <;> intro h
            · simp at h
              rcases h with h | h
              · exact sub_eq_zero.mp h
              · have : x = - (3 - √ 5) / 4 := by linarith only [h]
                have : ¬ x > 0 := by
                  simp [this]
                  apply sqrt_le_iff.mpr
                  constructor
                  all_goals norm_num
                contradiction
            · simp [h]

  -- general case : a * b * c > 0
  have hMax' (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : M (a, b, c) ≥ (11 + 5 * √5) / 2 ∧
      (M (a, b, c) = (11 + 5 * √5) / 2 ↔ ∃ t > 0, a = ((1 + √5) / 2) ^ (1 / (3 : ℝ)) * t ∧ c = ((1 + √5) / 2) ^ (1 / (3 : ℝ)) * t  ∧ b = ((3 - √5) / 2) ^ (1 / (3 : ℝ)) * t) := by
    -- The expression $M$ is homogeneous, therefore we can assume that $a b c=1$.
    let t := (a * b * c) ^ (1 / 3 : ℝ)
    let a' := a / t
    let b' := b / t
    let c' := c / t
    have hmulpos : 0 < a * b * c := by
      apply mul_pos ?_ hc
      exact mul_pos ha hb
    have ht : t > 0 := by exact rpow_pos_of_pos hmulpos (1 / 3 : ℝ)
    have htne : t ≠ 0 := by exact ne_of_gt ht
    have ha'pos : a' > 0 := by simp [a']; apply div_pos ha (rpow_pos_of_pos hmulpos _)
    have hb'pos : b' > 0 := by simp [b']; apply div_pos hb (rpow_pos_of_pos hmulpos _)
    have hc'pos : c' > 0 := by simp [c']; apply div_pos hc (rpow_pos_of_pos hmulpos _)
    have hmul' : a' * b' * c' = 1 := by
      simp [a', b', c']
      field_simp
      rw [←rpow_add hmulpos, ←rpow_add hmulpos]
      norm_num
    obtain h := hMax hM a' b' c' ha'pos hb'pos hc'pos hmul'
    have hMeq : M (a, b, c) = M (a', b', c') := by
      simp [hM, a', b', c']
      field_simp
    rw [hMeq]
    constructor
    · exact h.1
    · constructor <;> intro h'
      · apply h.2.mp at h'
        use t, ht
        nth_rw 1 1 1 [←h'.1, ←h'.2.1, ←h'.2.2]
        simp [a', b', c']
        rw [div_mul_cancel₀ _ htne, div_mul_cancel₀ _ htne, div_mul_cancel₀ _ htne]
        simp
      · obtain ⟨t', ⟨ht', h'⟩⟩ := h'
        have ht'' : t' ≥ 0 := by apply le_of_lt ht'
        have htne : t' ≠ 0 := by apply ne_of_gt ht'
        have : a' = ((1 + √5) / 2) ^ (1 / 3 : ℝ) ∧ c' = ((1 + √5) / 2) ^ (1 / 3 : ℝ) ∧ b' = ((3 - √5) / 2) ^ (1 / 3 : ℝ) := by
          have : t' = t := by
            simp [t, h'.1, h'.2.1, h'.2.2]
            rw [←hphi3]
            calc
              _ = (goldenRatio ^ (3 : ℝ)⁻¹ * goldenRatio ^ (3 : ℝ)⁻¹ * (1 / goldenRatio ^ 2) ^ (3 : ℝ)⁻¹ * t'^ 3) ^ (3 : ℝ)⁻¹ := by
                rw [mul_rpow, ←rpow_natCast _ 3, ←rpow_mul ht'', ←mul_rpow hphi1 hphi1, ←mul_rpow, ←sq, mul_div_cancel₀]
                · norm_num
                · apply ne_of_gt
                  exact sq_pos_of_pos gold_pos
                · exact mul_nonneg hphi1 hphi1
                · apply div_nonneg (by norm_num) (sq_nonneg _)
                · apply mul_nonneg
                  apply mul_nonneg hphi4 hphi4
                  apply rpow_nonneg
                  apply div_nonneg (by norm_num) (sq_nonneg _)
                · apply pow_nonneg ht''
              _ = _ := by ring_nf
          simp [a', b', c', ←this, h'.1, h'.2.1, h'.2.2]
          rw [mul_div_cancel_right₀ _ htne, mul_div_cancel_right₀ _ htne]
          simp
        exact h.2.mpr this

  -- finnaly, prove the result
  ext ⟨a, b, c⟩
  simp [hD]
  constructor <;> intro h
  · obtain ⟨⟨ha, ⟨hb, hc⟩⟩, hmin⟩ := h
    apply isMinOn_iff.mp at hmin
    have : M (a, b, c) = (11 + 5 * √5) / 2 := by
      apply le_antisymm
      · let a' := goldenRatio ^ (1 / 3 : ℝ)
        let b' := ((3 - √ 5) / 2) ^ (1 / 3 : ℝ)
        let c' := goldenRatio ^ (1 / 3 : ℝ)
        have ha' : a' > 0 := by
          simp [a']
          apply rpow_pos_of_pos gold_pos
        have hb' : b' > 0 := by
          simp only [b']
          rw [←hphi3]
          simp
          apply rpow_pos_of_pos
          apply inv_pos_of_pos
          apply add_pos gold_pos (by norm_num)
        have hc' : c' > 0 := by
          simp [c']
          apply rpow_pos_of_pos gold_pos
        have : (a', b', c') ∈ {x | 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2} := by
          simp only [Set.mem_setOf_eq, gold_pos, hb', ha', hc']
          simp
        obtain hmin := hmin (a', b', c') this
        apply le_of_le_of_eq hmin
        obtain h' := (hMax' a' b' c' ha' hb' hc').2.mpr
        have : ∃ t > 0, a' = ((1 + √5) / 2) ^ (1 / 3 : ℝ) * t ∧ c' = ((1 + √5) / 2) ^ (1 / 3 : ℝ) * t ∧ b' = ((3 - √5) / 2) ^ (1 / 3 : ℝ) * t := by
          use 1, by norm_num
          simp [a', b', c']
        exact h' this
      · apply (hMax' a b c ha hb hc).1
    obtain ⟨t, ⟨ht1, ⟨ha, ⟨hb, hc⟩⟩⟩⟩ := (hMax' a b c ha hb hc).2.mp this
    use t, ht1
    simp [ha, hb, hc, mul_comm]
  · obtain ⟨t, ⟨ht1, ⟨ha', ⟨hb', hc'⟩⟩⟩⟩ := h
    have ha : a > 0 := by
      simp [←ha']
      apply mul_pos ht1
      apply rpow_pos_of_pos gold_pos
    have hb : b > 0 := by
      simp [←hb']
      apply mul_pos ht1
      apply rpow_pos_of_pos
      rw [←hphi3]
      simp
      apply add_pos gold_pos (by norm_num)
    have hc : c > 0 := by
      simp [←hc']
      apply mul_pos ht1
      apply rpow_pos_of_pos gold_pos
    obtain h := hMax' a b c ha hb hc
    simp [ha, hb, hc]
    apply isMinOn_iff.mpr
    intro x hx
    simp at hx
    have : M x ≥ (11 + 5 * √5) / 2 := (hMax' x.1 x.2.1 x.2.2 hx.1 hx.2.1 hx.2.2).1
    apply le_of_eq_of_le ?_ this
    apply h.2.mpr
    use t, ht1
    rw [←ha', ←hb', ←hc']
    simp [mul_comm]
