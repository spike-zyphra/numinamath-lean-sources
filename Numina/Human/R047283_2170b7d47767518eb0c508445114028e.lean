import Mathlib

/- Given $a, b, c > 0$, and $abc = 1$, $\lambda (\lambda \geqslant 1)$ is a constant. Prove:
$$
\frac{1}{a+b+\lambda}+\frac{1}{b+c+\lambda}+\frac{1}{c+a+\lambda} \leqslant \frac{3}{2+\lambda},
$$

with equality holding if and only if $a=b=c=1$. -/
theorem inequalities_307946 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) (lambda : ℝ) (hl : 1 ≤ lambda) :
    3 / (2 + lambda) ≥ 1 / (a + b + lambda) + 1 / (b + c + lambda) + 1 / (c + a + lambda) ∧
    (3 / (2 + lambda) = 1 / (a + b + lambda) + 1 / (b + c + lambda) + 1 / (c + a + lambda) ↔
    (a = 1 ∧ b = 1 ∧ c = 1)) := by
  -- Prove that using “$\sum$” and “$\prod$” to denote cyclic sums and cyclic products, respectively, we have: $$ \begin{array}{l} \sum \frac{1}{a+b+\lambda} \leqslant \frac{3}{2+\lambda} \ \Leftrightarrow (2+\lambda)\left[\sum(a+b)(b+c)+4 \lambda \sum a+3 \lambda^{2}\right] \ \quad \leqslant 3\left[\prod(a+b)+\lambda \sum(a+b)(b+c)+2 \lambda^{2} \sum a+\lambda^{3}\right] \ \Leftrightarrow \left(2 \lambda^{2}-8 \lambda\right) \sum a+2(\lambda-1) \sum(a+b)(b+c)+ \ \quad 3 \prod(a+b)-6 \lambda^{2} \geqslant 0 . \end{array} $$
  field_simp
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : ((b + c + lambda + (a + b + lambda)) * (c + a + lambda) + (a + b + lambda) * (b + c + lambda)) * (2 + lambda) ≤
    3 * ((a + b + lambda) * (b + c + lambda) * (c + a + lambda)) ↔
    (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b) * (b + c) + (b + c) * (c + a) + (c + a) * (a + b)) + 3 * (a + b) * (b + c) * (c + a) - 6 * lambda ^ 2 ≥ 0 := by
    constructor
    · intro h
      apply sub_nonneg.mpr at h
      apply le_of_le_of_eq h
      ring
    · intro h
      apply sub_nonneg.mp
      apply le_of_le_of_eq h
      ring
  rw [this]
  have : 3 * ((a + b + lambda) * (b + c + lambda) * (c + a + lambda)) = ((b + c + lambda + (a + b + lambda)) * (c + a + lambda) + (a + b + lambda) * (b + c + lambda)) * (2 + lambda) ↔
    (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b) * (b + c) + (b + c) * (c + a) + (c + a) * (a + b)) + 3 * (a + b) * (b + c) * (c + a) - 6 * lambda ^ 2 = 0 := by
    constructor <;> intro h
    · apply sub_eq_zero.mpr at h
      rw [←h]
      ring
    · apply sub_eq_zero.mp
      rw [←h]
      ring
  rw [this]
  -- Notice that, $$ \begin{array}{l} \sum(a+b)(b+c)=\left(\sum a\right)^{2}+\sum a b \ =\left(\sum a\right)^{2}+\sum \frac{1}{a} \geqslant\left(\sum a\right)^{2}+\frac{9}{\sum a} \
  have sum_mul_eq : (a + b) * (b + c) + (b + c) * (c + a) + (c + a) * (a + b) = (a + b + c) ^ 2 + (1 / a + 1 / b + 1 / c) := by
    trans (a + b + c) ^ 2 + (a * b + b * c + c * a)
    · ring
    · rw [←habc]
      field_simp
      ring
  rw [sum_mul_eq]
  have cauchy : 1 / a + 1 / b + 1 / c ≥ 9 / (a + b + c) := by
    apply div_le_iff₀ ?_ |>.mpr
    · let f (i : Fin 3) := [1 / a, 1 / b, 1 / c].get i
      let g (i : Fin 3) := [a, b, c].get i
      let r (_ : Fin 3) := 1
      have hf : ∀ i ∈ Finset.univ, 0 ≤ f i := by
        intro i _
        simp [f]
        fin_cases i
        all_goals
          simp
          positivity
      have hg : ∀ i ∈ Finset.univ, 0 ≤ g i := by
        intro i _
        simp [g]
        fin_cases i
        all_goals
          simp
          positivity
      have hr : ∀ i ∈ Finset.univ, r i ^ 2 = f i * g i := by
        intro i _
        simp [f, g, r]
        fin_cases i
        all_goals
          field_simp
      obtain h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _ hf hg hr
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ] at h
      simp [f, g, r, ←add_assoc] at h
      norm_num at h
      simp [h]
    · positivity
  have cauchy_gt (h : a ≠ b ∨ b ≠ c) : 1 / a + 1 / b + 1 / c > 9 / (a + b + c) := by
    apply div_lt_iff₀ (by positivity) |>.mpr
    apply sub_pos.mp
    apply lt_of_lt_of_eq (b := (√(b / a) - √(a / b)) ^ 2 + (√(c / b) - √(b / c)) ^ 2 + (√(a / c) - √(c / a)) ^ 2)
    · rcases h with h | h
      · apply add_pos_of_pos_of_nonneg
        · apply add_pos_of_pos_of_nonneg
          · apply sq_pos_of_ne_zero
            by_contra h'
            apply sub_eq_zero.mp at h'
            apply Real.sqrt_inj (by positivity) (by positivity) |>.mp at h'
            field_simp at h'
            rw [←sq, ←sq] at h'
            apply pow_left_inj₀ (by positivity) (by positivity) (by simp) |>.mp at h'
            exact h.elim (Eq.symm h')
          · positivity
        · positivity
      · apply add_pos_of_pos_of_nonneg
        · apply add_pos_of_nonneg_of_pos
          · positivity
          · apply sq_pos_of_ne_zero
            by_contra h'
            apply sub_eq_zero.mp at h'
            apply Real.sqrt_inj (by positivity) (by positivity) |>.mp at h'
            field_simp at h'
            rw [←sq, ←sq] at h'
            apply pow_left_inj₀ (by positivity) (by positivity) (by simp) |>.mp at h'
            exact h.elim (Eq.symm h')
        · positivity
    · rw [sub_sq, sub_sq, sub_sq, Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt]
      simp [mul_assoc]
      rw [←Real.sqrt_mul, ←Real.sqrt_mul, ←Real.sqrt_mul]
      · rw [show c / b * (b / c) = 1 by field_simp]
        rw [show a / c * (c / a) = 1 by field_simp]
        rw [show b / a * (a / b) = 1 by field_simp]
        simp
        ring_nf
        rw [mul_inv_cancel₀, mul_inv_cancel₀, mul_inv_cancel₀]
        ring
        all_goals positivity
      all_goals positivity
  have apply_cauchy : (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b + c) ^ 2 + (1 / a + 1 / b + 1 / c)) +
      3 * (a + b) * (b + c) * (c + a) - 6 * lambda ^ 2 ≥ (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b + c) ^ 2 + 9 / (a + b + c)) +
      3 * (a + b) * (b + c) * (c + a) - 6 * lambda ^ 2 := by
    gcongr
    simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, sub_nonneg, hl]
  -- apply And.imp_left (fun h => le_trans h apply_cauchy)
  have apply_cauchy_gt (h : a ≠ b ∨ b ≠ c) (hl : lambda > 1) : (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b + c) ^ 2 + (1 / a + 1 / b + 1 / c)) +
      3 * (a + b) * (b + c) * (c + a) - 6 * lambda ^ 2 > (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b + c) ^ 2 + 9 / (a + b + c)) +
      3 * (a + b) * (b + c) * (c + a) - 6 * lambda ^ 2 := by
    gcongr
    · simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, sub_pos, hl]
    · exact cauchy_gt h
  -- \prod(a+b)=\sum a^{2}(b+c)+2 a b c \ \geqslant 2 \sum a^{2} \sqrt{b c}+2=2\left(\sum a\right) \sqrt{a}+2 \ \geqslant \frac{2}{3}\left(\sum a\right) \sum \sqrt{a}+2 \ \geqslant 2 \sum a+2 \end{array} $$
  have prod_add_eq : 3 * (a + b) * (b + c) * (c + a) = 3 * (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b)) + 6 := by
    trans 3 * (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b)) + 6 * (a * b * c)
    · ring
    · simp [habc]
  have ham_gm {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
      a ^ 2 * (b + c) ≥ 2 * a ^ 2 * √(b * c) := by
    apply sub_nonneg.mp
    trans a ^ 2 * (√b - √c) ^ 2
    · positivity
    · apply le_of_eq
      rw [sub_sq, Real.sq_sqrt, Real.sq_sqrt, Real.sqrt_mul]
      · ring
      all_goals positivity
  have ham_gm_gt {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : b ≠ c) :
      a ^ 2 * (b + c) > 2 * a ^ 2 * √(b * c) := by
    apply sub_pos.mp
    apply lt_of_lt_of_eq (b := a ^ 2 * (√b - √c) ^ 2)
    · apply mul_pos
      · positivity
      · apply sq_pos_of_ne_zero
        by_contra h'
        apply sub_eq_zero.mp at h'
        apply Real.sqrt_inj (le_of_lt hb) (le_of_lt hc) |>.mp at h'
        exact h.elim h'
    · rw [sub_sq, Real.sq_sqrt, Real.sq_sqrt, Real.sqrt_mul]
      · ring
      all_goals positivity
  have ham_gm' {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
      a ^ 2 * (b + c) ≥ 2 * a * √a * √(a * b * c) := by
    apply le_trans ?_ (ham_gm ha hb hc)
    rw [Real.sqrt_mul, Real.sqrt_mul, Real.sqrt_mul]
    trans 2 * a * (√a * √a) * √b * √c
    · apply le_of_eq
      ring
    · rw [Real.mul_self_sqrt]
      · apply le_of_eq
        ring
      · positivity
    all_goals positivity
  have ham_gm_gt' {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : b ≠ c) :
      a ^ 2 * (b + c) > 2 * a * √a * √(a * b * c) := by
    apply lt_of_eq_of_lt ?_ (ham_gm_gt ha hb hc h)
    rw [Real.sqrt_mul, Real.sqrt_mul, Real.sqrt_mul]
    trans 2 * a * (√a * √a) * √b * √c
    · ring
    · rw [Real.mul_self_sqrt]
      · ring
      · positivity
    all_goals positivity
  have am_gm : a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b) ≥ 2 * (a * √a + b * √b + c * √c) := by
    trans 2 * a * √a * √(a * b * c) + 2 * b * √b * √(b * c * a) + 2 * c * √c * √(c * a * b)
    · rel [ham_gm' ha hb hc, ham_gm' hb hc ha, ham_gm' hc ha hb]
    · apply le_of_eq
      ring_nf
      simp [habc]
  have am_gm_gt (h : a ≠ b ∨ b ≠ c) : a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b) > 2 * (a * √a + b * √b + c * √c) := by
    apply lt_of_eq_of_lt (b := 2 * a * √a * √(a * b * c) + 2 * b * √b * √(b * c * a) + 2 * c * √c * √(c * a * b))
    · ring_nf
      simp [habc]
    · rcases h with h | h
      · apply add_lt_add_of_le_of_lt
        · rel [ham_gm' ha hb hc, ham_gm' hb hc ha]
        · apply ham_gm_gt' hc ha hb h
      · apply add_lt_add_of_lt_of_le
        · apply add_lt_add_of_lt_of_le
          · apply ham_gm_gt' ha hb hc h
          · rel [ham_gm' hb hc ha]
        · rel [ham_gm' hc ha hb]
  have chebyshev : a * √a + b * √b + c * √c ≥ 1 / 3 * (a + b + c) * (√a + √b + √c) := by
    let f (i : Fin 3) := [a, b, c].get i
    let g (i : Fin 3) := [√a, √b, √c].get i
    have hfg' {i : Fin 3} : g i = √(f i) := by
      unfold f g
      fin_cases i
      all_goals rfl
    have hfg : Monovary f g := by
      unfold Monovary
      intro i j h
      rw [hfg', hfg'] at h
      apply le_of_lt
      apply Real.sqrt_lt_sqrt_iff ?_ |>.mp h
      unfold f
      fin_cases i
      all_goals positivity
    obtain h := Monovary.sum_mul_sum_le_card_mul_sum hfg
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ] at h
    simp [f, g, ←add_assoc] at h
    linarith only [h]
  have chebyshev' : a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b) ≥ 2 * (a + b + c) := by
    apply le_trans ?_ am_gm
    simp only [Nat.ofNat_pos, mul_le_mul_left]
    apply le_trans ?_ chebyshev
    trans 1 / 3 * (a + b + c) * (3 * (a * b * c) ^ (1 / 6 : ℝ))
    · rw [habc, Real.one_rpow]
      field_simp
    · gcongr
      obtain h := Real.geom_mean_le_arith_mean3_weighted (w₁ := 1 / 3) (w₂ := 1 / 3) (w₃ := 1 / 3) (p₁ := √a) (p₂ := √b) (p₃ := √c) (by simp) (by simp) (by simp) (by positivity) (by positivity) (by positivity) (by norm_num)
      field_simp at h
      apply le_div_iff₀ (by simp) |>.mp at h
      apply le_of_eq_of_le ?_ h
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      rw [←Real.rpow_mul, ←Real.rpow_mul, ←Real.rpow_mul, Real.mul_rpow, Real.mul_rpow]
      rw [show 1 / 2 * (1 / 3) = (1 / 6 : ℝ) by norm_num]
      ring
      all_goals positivity
  have chebyshev_gt' (h : a ≠ b ∨ b ≠ c) : a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b) > 2 * (a + b + c) := by
    apply lt_of_le_of_lt ?_ (am_gm_gt h)
    simp only [Nat.ofNat_pos, mul_le_mul_left]
    apply le_trans ?_ chebyshev
    trans 1 / 3 * (a + b + c) * (3 * (a * b * c) ^ (1 / 6 : ℝ))
    · rw [habc, Real.one_rpow]
      field_simp
    · gcongr
      obtain h := Real.geom_mean_le_arith_mean3_weighted (w₁ := 1 / 3) (w₂ := 1 / 3) (w₃ := 1 / 3) (p₁ := √a) (p₂ := √b) (p₃ := √c) (by simp) (by simp) (by simp) (by positivity) (by positivity) (by positivity) (by norm_num)
      field_simp at h
      apply le_div_iff₀ (by simp) |>.mp at h
      apply le_of_eq_of_le ?_ h
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      rw [←Real.rpow_mul, ←Real.rpow_mul, ←Real.rpow_mul, Real.mul_rpow, Real.mul_rpow]
      rw [show 1 / 2 * (1 / 3) = (1 / 6 : ℝ) by norm_num]
      ring
      all_goals positivity
  have apply_chebyshev : (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b + c) ^ 2 + (1 / a + 1 / b + 1 / c)) +
      3 * (a + b) * (b + c) * (c + a) - 6 * lambda ^ 2 ≥  (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b + c) ^ 2 + 9 / (a + b + c)) +
      (6 * (a + b + c) + 6) - 6 * lambda ^ 2 := by
    apply le_trans ?_ apply_cauchy
    rw [prod_add_eq, ←ge_iff_le]
    trans (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b + c) ^ 2 + 9 / (a + b + c)) +
      (3 * (2 * (a + b + c)) + 6) - 6 * lambda ^ 2
    · rel [chebyshev']
    · apply le_of_eq
      ring
  have apply_chebyshev_gt (h : a ≠ b ∨ b ≠ c) : (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b + c) ^ 2 + (1 / a + 1 / b + 1 / c)) +
      3 * (a + b) * (b + c) * (c + a) - 6 * lambda ^ 2 >  (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b + c) ^ 2 + 9 / (a + b + c)) +
      (6 * (a + b + c) + 6) - 6 * lambda ^ 2 := by
    apply lt_of_lt_of_le ?_ (apply_cauchy)
    rw [prod_add_eq, ←gt_iff_lt]
    apply lt_of_eq_of_lt (b := (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b + c) ^ 2 + 9 / (a + b + c)) +
      (3 * (2 * (a + b + c)) + 6) - 6 * lambda ^ 2)
    · ring
    · gcongr
      exact chebyshev_gt' h
  -- Let ( a+b+c=t ).
  let t := a + b + c
  have ht : t = a + b + c := by rfl
  have ht_ge_3 : t ≥ 3 := by
    obtain h := Real.geom_mean_le_arith_mean3_weighted (w₁ := 1 / 3) (w₂ := 1 / 3) (w₃ := 1 / 3) (p₁ := a) (p₂ := b) (p₃ := c) (by simp) (by simp) (by simp) (by positivity) (by positivity) (by positivity) (by norm_num)
    field_simp at h
    apply le_div_iff₀ (by simp) |>.mp at h
    apply le_of_eq_of_le ?_ h
    rw [←Real.mul_rpow, ←Real.mul_rpow, habc, Real.one_rpow, one_mul]
    all_goals positivity
  -- Thus, we only need to prove: $$ \begin{array}{l} 2(\lambda-1) t^{2}+\frac{18(\lambda-1)}{t}+ \ \left(2 \lambda^{2}-8 \lambda+6\right) t+6\left(1-\lambda^{2}\right) \geqslant 0 \ \Leftrightarrow (\lambda-1) f(t) \geqslant 0, \end{array} $$
  have subset_t : (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b + c) ^ 2 + (1 / a + 1 / b + 1 / c)) +
      3 * (a + b) * (b + c) * (c + a) - 6 * lambda ^ 2 ≥  2 * (lambda - 1) * t ^ 2 + 18 * (lambda - 1) / t +
      (2 * lambda ^ 2 - 8 * lambda + 6) * t + 6 * (1 - lambda ^ 2) := by
    apply le_trans ?_ apply_chebyshev
    unfold t
    apply le_of_eq
    ring
  have subset_t_gt (h : a ≠ b ∨ b ≠ c) : (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b + c) ^ 2 + (1 / a + 1 / b + 1 / c)) +
      3 * (a + b) * (b + c) * (c + a) - 6 * lambda ^ 2 >  2 * (lambda - 1) * t ^ 2 + 18 * (lambda - 1) / t +
      (2 * lambda ^ 2 - 8 * lambda + 6) * t + 6 * (1 - lambda ^ 2) := by
    apply lt_of_le_of_lt ?_ (apply_chebyshev_gt h)
    unfold t
    apply le_of_eq
    ring
  -- where ( f(t)=t^{3}+(\lambda-3) t^{2}-3(\lambda+1) t+9 ).
  let f (t : ℝ) := t ^ 3 + (lambda - 3) * t ^ 2 - 3 * (lambda + 1) * t + 9
  have hf : 2 * (lambda - 1) * f t / t = 2 * (lambda - 1) * t ^ 2 + 18 * (lambda - 1) / t +
      (2 * lambda ^ 2 - 8 * lambda + 6) * t + 6 * (1 - lambda ^ 2) := by
    unfold f
    field_simp
    ring
  -- When (\lambda=1), inequality (1) is clearly true.
  have f_t_nonneg : 2 * (lambda - 1) * t ^ 2 + 18 * (lambda - 1) / t +
      (2 * lambda ^ 2 - 8 * lambda + 6) * t + 6 * (1 - lambda ^ 2) ≥ 0 ↔ f t ≥ 0 ∨ lambda = 1 := by
    rw [←hf]
    constructor <;> intro h
    · apply div_nonneg_iff.mp at h
      have : ¬ t ≤ 0 := by push_neg; positivity
      simp [this] at h
      obtain h := h.1
      apply mul_nonneg_iff.mp at h
      by_cases hl : lambda > 1
      · have : ¬ 2 * (lambda - 1) ≤ 0 := by push_neg; linarith only [hl]
        simp [this] at h
        left
        exact h.2
      · push_neg at hl
        have : lambda = 1 := by
          apply le_antisymm hl
          assumption
        simp [this]
    · rcases h with h | h
      · apply div_nonneg
        · apply mul_nonneg
          · simp
            exact hl
          · exact h
        · positivity
      · simp [h]
  have h_t_pos : 2 * (lambda - 1) * t ^ 2 + 18 * (lambda - 1) / t +
      (2 * lambda ^ 2 - 8 * lambda + 6) * t + 6 * (1 - lambda ^ 2) > 0 ↔ f t > 0 ∧ lambda ≠ 1 := by
    rw [←hf]
    constructor <;> intro h
    · apply div_pos_iff.mp at h
      have : ¬ t < 0 := by push_neg; positivity
      simp [this] at h
      obtain h := h.1
      apply mul_pos_iff.mp at h
      have : ¬ 2 * (lambda - 1) < 0 := by push_neg; simp; assumption
      simp [this] at h
      obtain ⟨h₁, h₂⟩ := h
      constructor
      · exact h₂
      · apply ne_of_gt h₁
    · apply div_pos
      · apply mul_pos
        · simp
          apply lt_of_le_of_ne hl
          symm
          exact h.2
        · exact h.1
      · positivity
  --When (\lambda&gt;1), $$ f^{\prime}(t)=3 t^{2}+2(\lambda-3) t-3(\lambda+1) $$
  have hf' {t : ℝ} : f t = (t - 3) * (t ^ 2 + lambda * t - 3) := by
    unfold f
    ring
  -- is a quadratic function in (t), whose graph opens upwards, and the axis of symmetry is $$ t=\frac{3-\lambda}{3} \quad \text{and} \quad f^{\prime}(3)&gt;0.
  -- $$ Therefore, (f(t)) is an increasing function, and (f(t) \geqslant f(3)=0).
  have h_f_t_nonneg : f t ≥ 0 := by
    rw [hf']
    apply mul_nonneg
    · simp
      exact ht_ge_3
    · nlinarith only [ht_ge_3, hl]
  have h_f_t_pos (ht : t > 3) : f t > 0 := by
    rw [hf']
    apply mul_pos
    · simp
      exact ht
    · nlinarith only [ht_ge_3, hl]
  -- Hence, inequality (1) is proved.
  have res : (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b + c) ^ 2 + (1 / a + 1 / b + 1 / c)) +
      3 * (a + b) * (b + c) * (c + a) - 6 * lambda ^ 2 ≥ 0 := by
    apply le_trans ?_ subset_t
    apply f_t_nonneg.mpr
    left
    exact h_f_t_nonneg
  have res_gt (h : a ≠ b ∨ b ≠ c) : (2 * lambda ^ 2 - 8 * lambda) * (a + b + c) + 2 * (lambda - 1) * ((a + b + c) ^ 2 + (1 / a + 1 / b + 1 / c)) +
      3 * (a + b) * (b + c) * (c + a) - 6 * lambda ^ 2 > 0 := by
    apply lt_of_le_of_lt ?_ (subset_t_gt h)
    apply f_t_nonneg.mpr
    left
    exact h_f_t_nonneg
  -- Thus, the inequality holds with equality if and only if (a=b=c=1).
  constructor
  · exact res
  · constructor <;> intro h
    · have : a = b ∧ b = c := by
        by_contra h'
        have : a ≠ b ∨ b ≠ c := by
          push_neg at h'
          by_cases ha : a = b
          · apply h' at ha
            simp [ha]
          · simp [ha]
        apply res_gt at this
        rw [h] at this
        apply lt_self_iff_false _ |>.mp this
      rw [this.1, this.2] at habc
      simp [this.1, this.2]
      have : c ^ 3 = 1 := by
        rw [←habc]
        ring
      apply pow_eq_one_iff_of_nonneg ?_ ?_ |>.mp this
      all_goals positivity
    · simp [h.1, h.2.1, h.2.2]
      ring
