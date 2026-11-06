import Mathlib

open Real Finset


/- If $a,$ $b,$ $c,$ $x,$ $y,$ and $z$ are positive and $a^2 + b^2 + c^2 = 25,$ $x^2 + y^2 + z^2 = 36,$ and $ax + by + cz = 30,$ compute $$\frac{a + b + c}{x + y + z}.$$ -/
theorem algebra_16765
    (a b c x y z : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : a^2 + b^2 + c^2 = 25)
    (h2 : x^2 + y^2 + z^2 = 36)
    (h3 : a * x + b * y + c * z = 30) :
    (a + b + c) / (x + y + z) = 5 / 6 := by

  -- aux lemma, two variable AM-GM inequality, equality condition
  have l_amgm (a b : ℝ) (ha : a > 0) (hb : b > 0) :
    2 * a * b ≤ a ^ 2 + b ^ 2 ∧
    (2 * a * b = a ^ 2 + b ^ 2 → a = b) := by
    constructor
    . have : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
      ring_nf at this
      linarith
    . intro h
      by_contra! h_contra
      have : (a - b) ^ 2 > 0 := sq_pos_iff.mpr (sub_ne_zero_of_ne h_contra)
      ring_nf at this
      linarith

  have l_ineq_add_eqcond {a b c d : ℝ} {f g : Prop}
      (h1 : a ≤ b) (h1' : a = b → f)
      (h2 : c ≤ d) (h2' : c = d → g)
      (ha : a > 0) (hc : c > 0) :
      a + c ≤ b + d ∧ (a + c = b + d → f ∧ g) := by
    constructor
    . exact add_le_add h1 h2
    . intro h
      have : a = b ∧ c = d := by
        constructor
        . by_contra! h_contra
          have : a < b := lt_of_le_of_ne h1 h_contra
          have : a + c < b + d := add_lt_add_of_lt_of_le this h2
          linarith
        . by_contra! h_contra
          have : c < d := lt_of_le_of_ne h2 h_contra
          have : a + c < b + d := add_lt_add_of_le_of_lt h1 this
          linarith
      simp [this, h1', h2']


  -- lemma, equality condition of Cauchy-Schwarz inequality
  have l_cauchy_eq (a b c x y z : ℝ)
      (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
      (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
      : (a * x + b * y + c * z) ^ 2 = (a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2) → ∃ k, a / x = k ∧ b / y = k ∧ c / z = k := by

    obtain ⟨ineq1, h1⟩ := l_amgm (a * y) (b * x) (mul_pos ha hy) (mul_pos hb hx)
    obtain ⟨ineq2, h2⟩ := l_amgm (a * z) (c * x) (mul_pos ha hz) (mul_pos hc hx)
    obtain ⟨ineq3, h3⟩ := l_amgm (b * z) (c * y) (mul_pos hb hz) (mul_pos hc hy)
    ring_nf at ineq1 h1 ineq2 h2 ineq3 h3

    have ⟨ineq', h'⟩ := l_ineq_add_eqcond ineq1 h1 ineq2 h2 ?_ ?_
    have ⟨_, h_eqcond⟩ := l_ineq_add_eqcond ineq' h' ineq3 h3 ?_ ?_
    ring_nf at h_eqcond

    intro h
    apply_fun fun t => t - a ^ 2 * x ^ 2 - b ^ 2 * y ^ 2 - c ^ 2 * z ^ 2 at h
    ring_nf at h

    have : (a * y = b * x ∧ a * z = x * c) ∧ b * z = y * c := by
      apply h_eqcond
      convert h using 1
      . rw [show a * y * b * x * 2 = a * x * b * y * 2 by ring_nf,
            show a * x * z * c * 2 = a * x * c * z * 2 by ring_nf,
            show y * b * z * c * 2 = b * y * c * z * 2 by ring_nf]
      . linarith
    obtain ⟨⟨hr1, hr2⟩⟩  := this

    set k := a / x with hk
    use k
    exact ⟨rfl, by field_simp [hk, hr1], by field_simp [hk,hr2, mul_comm]⟩
    any_goals apply add_pos
    all_goals
      repeat apply mul_pos
      all_goals simp only [ha, hb, hc, hx, hy, hz, zero_lt_two]

  -- By the Cauchy-Schwarz inequality, $(a^2 + b^2 + c^2)(x^2 + y^2 + z^2) \ge (ax + by + cz)^2.$ This becomes $25 \cdot 36 \ge 30^2.$  Since $25 \cdot 36 = 900 = 30^2,$ we get equality.
  have : (a * x + b * y + c * z) ^ 2 = (a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2) := by
    rw [h1, h2, h3]
    norm_num

  -- From the equality condition in Cauchy-Schwarz, $\frac{a}{x} = \frac{b}{y} = \frac{c}{z}.$Let $k = \frac{a}{x} = \frac{b}{y} = \frac{c}{z}.$
  obtain ⟨k, ⟨hk1, hk2, hk3⟩⟩ := l_cauchy_eq a b c x y z ha hb hc hx hy hz this

  -- Then $a = kx,$ $b = ky$ and $c = kz,$ so $a^2 + b^2 + c^2 = k^2 x^2 + k^2 y^2 + k^2 z^2 = k^2 (x^2 + y^2 + z^2).$
  have : a ^ 2 + b ^ 2 + c ^ 2 = k ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    apply_fun fun t => t * x at hk1
    rw [div_mul_cancel₀ _ (by linarith)] at hk1
    apply_fun fun t => t * y at hk2
    rw [div_mul_cancel₀ _ (by linarith)] at hk2
    apply_fun fun t => t * z at hk3
    rw [div_mul_cancel₀ _ (by linarith)] at hk3
    rw [hk1, hk2, hk3]
    linarith

  -- Then $36k^2 = 25,$ so $k^2 = \frac{25}{36},$ which means $k = \frac{5}{6}.$
  have : k = (5 : ℝ) / 6 := by
    rw [h1, h2] at this
    have : k ^ 2 = (5 / 6) ^ 2 := by field_simp; linarith
    apply (sq_eq_sq_iff_abs_eq_abs k (5 / 6)).mp at this
    rw [← hk1, abs_of_pos, abs_of_pos, hk1] at this
    exact this
    all_goals exact div_pos (by linarith) (by linarith)

  -- Therefore, $$\frac{a + b + c}{x + y + z} = \boxed{\frac{5}{6}}.$$
  apply_fun fun t => t * x at hk1
  rw [div_mul_cancel₀ _ (by linarith)] at hk1
  apply_fun fun t => t * y at hk2
  rw [div_mul_cancel₀ _ (by linarith)] at hk2
  apply_fun fun t => t * z at hk3
  rw [div_mul_cancel₀ _ (by linarith)] at hk3
  rw [hk1, hk2, hk3, ← mul_add, ← mul_add, mul_div_cancel_right₀, this]
  linarith
