import Mathlib

/- Prove that for any positive integers $p, q$ such that $\sqrt{11}>\frac{p}{q}$, the following inequality holds:

$$
\sqrt{11}-\frac{p}{q}>\frac{1}{2 p q}
$$ -/
theorem inequalities_238423 (p q : ℕ) (hp : p > 0) (hq : q > 0)
    (h : Real.sqrt 11 > (p / q : ℝ)) :
    Real.sqrt 11 - (p / q : ℝ) > 1 / (2 * p * q) := by

  -- lemma, less than of square less than square, if the larger is nonnegative
  have l_lt_of_sq_lt_sq (a b : ℝ) (hb : 0 ≤ b) (h : a ^ 2 < b ^ 2) : a < b := by
    have t1 : |a| < b := abs_lt_of_sq_lt_sq h hb
    have t2 : a ≤ |a| := le_abs_self a
    linarith only [t1, t2]

  -- lemma, square less than square of less than, for nonnegative numbers
  have l_sq_lt_sq_of_lt (a b : ℝ) (ha : 0 ≤ a) (h : a < b) : a ^ 2 < b ^ 2 := by
    have : |a| < |b| := by
      convert h <;> apply abs_of_nonneg (by linarith)
    exact sq_lt_sq.mpr this

  -- lemma, eq of square eq square, for nonnegative numbers
  have l_eq_of_sq_eq_sq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 = b ^ 2 → a = b := by
    intro h
    apply_fun (√ ·) at h
    convert h
    <;> field_simp

  -- We can assume that $p$ and $q$ are coprime,
  wlog h_wlog : p.Coprime q generalizing p q
  . have : ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x.Coprime y ∧ (x / y : ℝ) = p / q ∧ x * y ≤ p * q := by
      let g := p.gcd q
      let x := p / g
      let y := q / g
      have hg : g ≠ 0 := by refine Nat.gcd_ne_zero_left (by positivity)
      use x, y
      have t1 : 0 < x := Nat.div_gcd_pos_of_pos_left q hp
      have t2 : 0 < y := Nat.div_gcd_pos_of_pos_right p hq
      have t3 : x.Coprime y := by
        refine Nat.coprime_div_gcd_div_gcd ?_
        exact Nat.gcd_pos_of_pos_left q hp
      have t4 : (x / y : ℝ) = p / q := by
        dsimp [x, y]
        rw [Nat.cast_div, Nat.cast_div]
        . refine div_div_div_cancel_right₀ (by norm_cast) (p : ℝ) q
        any_goals norm_cast
        exact Nat.gcd_dvd_right _ _
        exact Nat.gcd_dvd_left _ _
      have t5 : x * y ≤ p * q := by
        gcongr <;> exact Nat.div_le_self _ _
      exact ⟨t1, t2, t3, t4, t5⟩
    obtain ⟨x, y, hx, hy, hcop, heq, hle⟩ := this
    specialize this x y hx hy (by linarith) hcop
    have : 1 / (2 * x * y : ℝ) ≥ 1 / (2 * p * q) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      norm_cast; linarith only [hle]
    linarith

  -- since both sides of first inequality are positive, we can change it to $11 q^{2}>p^{2}$.
  have r1 : 11 * q ^ 2 > p ^ 2 := by
    have := l_sq_lt_sq_of_lt _ _ (by positivity) (gt_iff_lt.mpr h)
    field_simp at this
    apply (div_lt_iff₀ (by positivity)).mp at this
    norm_cast at this

  -- The same way we can change second inequality: $$ 11 p^{2} q^{2}>p^{4}+p^{2}+\frac{1}{4} $$
  suffices : 11 * p ^ 2 * q ^ 2 > p ^ 4 + p ^ 2 + (1 / 4 : ℝ)
  . have t1 : (1 / 2 : ℝ) + p ^ 2 < √ 11 * p * q := by
      apply Real.sqrt_lt_sqrt (by positivity) at this
      convert this using 1
      . apply l_eq_of_sq_eq_sq
        any_goals positivity
        field_simp; ring
      field_simp
    apply (div_lt_div_iff_of_pos_right (show 0 < (p : ℝ) * q by positivity)).mpr at t1
    rw [add_div, div_div, ← mul_assoc,
        show (p : ℝ) ^ 2 / (p * q) = p / q by field_simp; ring,
        show √ 11 * (p : ℝ) * q / (p * q) = √ 11 by field_simp; ring] at t1
    linarith only [t1]

  -- To see this one holds, we will prove stronger one: $$ 11 p^{2} q^{2} \geq p^{4}+2 p^{2} \text {. } $$
  suffices : 11 * p ^ 2 * q ^ 2 ≥ p ^ 4 + 2 * p ^ 2
  . rify at this
    have t1 : 2 * p ^ 2 > p ^ 2 + (1 / 4 : ℝ) := by
      have : 1 ≤ (p : ℝ) ^ 2 := by norm_cast; exact Nat.one_le_pow 2 p hp
      linarith
    linarith only [t1, this]

  -- dividing this inequality by $p^{2}$ we get $11 q^{2} \geq p^{2}+2$,
  suffices : 11 * q ^ 2 ≥ p ^ 2 + 2
  . apply (mul_le_mul_iff_of_pos_right (show 0 < p ^ 2 by positivity)).mpr at this
    linarith only [this]

  --  since we already know that $11 q^{2}>p^{2}$ we only have to see, that $11 q^{2}$ can't be equal to $p^{2}+1$.
  suffices : 11 * q ^ 2 ≠ p ^ 2 + 1
  . omega

  -- Since we know that the only reminders of squares $(\bmod 11)$ are $0,1,3,4,5$ and $9, p^{2}+1$ can't be divisible by 11 , and therefore $11 q^{2} \neq p^{2}+1$.
  by_contra! h_contra
  apply_fun (· % 11) at h_contra
  rw [show (11 * q ^ 2) % 11 = 0 by simp] at h_contra
  have : 0 ≠ (p ^ 2 + 1) % 11 := by
    rw [pow_two, Nat.add_mod, Nat.mul_mod]
    have := Nat.mod_lt p (show 0 < 11 by norm_num)
    interval_cases (p % 11)
    all_goals norm_num
  contradiction
