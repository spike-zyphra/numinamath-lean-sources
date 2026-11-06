import Mathlib

/- Let $x, y$ and $z$ be positive numbers. Prove that

$$
\frac{x}{\sqrt{\sqrt[4]{y}+\sqrt[4]{z}}}+\frac{y}{\sqrt{\sqrt[4]{z}+\sqrt[4]{x}}}+
\frac{z}{\sqrt{\sqrt[4]{x}+\sqrt[4]{y}}} \geq \frac{\sqrt[4]{(\sqrt{x}+\sqrt{y}+\sqrt{z})^{7}}}{\sqrt{2 \sqrt{27}}}
$$ -/
theorem inequalities_604913 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / √ ((y ^ ((1 : ℝ) / 4) + z ^ ((1 : ℝ) / 4)) ) +
    y / √ ((z ^ ((1 : ℝ) / 4) + x ^ ((1 : ℝ) / 4)) ) +
    z / √ ((x ^ ((1 : ℝ) / 4) + y ^ ((1 : ℝ) / 4)) ) ≥
    ((√ x + √ y + √ z) ^ ((7 : ℝ) / 4)) / √ (2 * √ 27) := by
  -- for positive number u, exist positive v such that v^2 = u
  have ex_sqrt{u:ℝ}(hu: 0 < u): ∃v, 0 < v ∧ u = v^2 := by
    use √u
    simp [hu, Real.sq_sqrt (le_of_lt hu)]
  -- (u^2)^(1/4) = √u
  have sq_pow_14{u:ℝ}(hu: 0 < u): (u^2)^(1/4: ℝ) = √u := by
    simp [← Real.rpow_natCast_mul (le_of_lt hu), Real.sqrt_eq_rpow]
    norm_num
  -- let x = a^2, y = b^2, z = c^2, and simplify the inequality.
  rcases (ex_sqrt hx) with ⟨a, ha, rfl⟩
  rcases (ex_sqrt hy) with ⟨b, hb, rfl⟩
  rcases (ex_sqrt hz) with ⟨c, hc, rfl⟩
  simp only [sq_pow_14 ha, sq_pow_14 hb, sq_pow_14 hc, Real.sqrt_sq (le_of_lt ha),
  Real.sqrt_sq (le_of_lt hb), Real.sqrt_sq (le_of_lt hc)]
  -- recall that Cauchy-Schwarz inequality says,
  -- (u1^2+u2^2+u3^2)(v1^2+v2^2+v3^2) ≥ (u1v1 + u2v2 + u3v3)^2
  have cauchy_schwarz_3{u1 u2 u3 v1 v2 v3: ℝ}:
    (u1^2+u2^2+u3^2)*(v1^2+v2^2+v3^2) ≥ (u1*v1 + u2*v2 + u3*v3)^2 := by
    let u: ℕ → ℝ
      | 0 => u1
      | 1 => u2
      | 2 => u3
      | n+3 => 0
    let v: ℕ → ℝ
      | 0 => v1
      | 1 => v2
      | 2 => v3
      | n+3 => 0
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range 3) u v
    simp [Finset.sum_range_succ] at this
    dsimp [u,v] at this; exact this
  -- let d1 denote √(√b+√c), d2 denote √(√c+√a), d3 denote √(√a+√b)
  set d1 := √(√b+√c) with d1_def
  have d1_nng: 0 ≤ d1 := by
    simp [d1_def]
  have d1_pos: 0 < d1 := by
    simp [d1_def]
    linarith [Real.sqrt_pos_of_pos hb, Real.sqrt_pos_of_pos hc]
  set d2 := √(√c+√a) with d2_def
  have d2_nng: 0 ≤ d2 := by
    simp [d2_def]
  have d2_pos: 0 < d2 := by
    simp [d2_def]
    linarith [Real.sqrt_pos_of_pos hc, Real.sqrt_pos_of_pos ha]
  set d3 := √(√a+√b) with d3_def
  have d3_nng: 0 ≤ d3 := by
    simp [d3_def]
  have d3_pos: 0 < d3 := by
    simp [d3_def]
    linarith [Real.sqrt_pos_of_pos ha, Real.sqrt_pos_of_pos hb]
  -- use cauchy-shcwarz inequality, a^2/d1 + b^2/d2 + c^2/d3 ≥ (a+b+c)^2/(d1+d2+d3)
  have c_s_apply_1: a^2/d1 + b^2/d2 + c^2/d3 ≥ (a+b+c)^2 / (d1+d2+d3) := by
    set u1 := a/√d1 with u1_def
    set u2 := b/√d2 with u2_def
    set u3 := c/√d3 with u3_def
    have hu1: a^2/d1 = u1^2 := by
      simp [u1_def, div_pow, Real.sq_sqrt d1_nng]
    have hu2: b^2/d2 = u2^2 := by
      simp [u2_def, div_pow, Real.sq_sqrt d2_nng]
    have hu3: c^2/d3 = u3^2 := by
      simp [u3_def, div_pow, Real.sq_sqrt d3_nng]
    -- therefore by cauchy-schwarz inequality,
    -- (a^2/d1 + b^2/d2 + c^2/d3) (d1+d2+d3) ≥ (a+b+c)^2
    have: (u1^2+u2^2+u3^2) * (d1+d2+d3) ≥ (u1*√d1 + u2*√d2 + u3*√d3)^2 := by
      nth_rw 1 [← Real.sq_sqrt d1_nng, ← Real.sq_sqrt d2_nng, ← Real.sq_sqrt d3_nng]
      apply cauchy_schwarz_3
    rw [← hu1, ← hu2, ← hu3] at this
    apply (div_le_iff₀ ?_).mpr ?_
    · linarith [d1_pos, d2_pos, d3_pos]
    · apply le_trans (le_of_eq ?_) this
      congr 1
      simp [u1_def, u2_def, u3_def]
      field_simp [d1_pos, d2_pos, d3_pos]
  -- also, by cauchy-schwarz inequality, we can prove
  -- √u1 + √u2 + √u3 ≤ √(3 (u1+u2+u3)), for positive u1,u2,u3.
  have c_s_apply_2{u1 u2 u3: ℝ}(hu1: 0 < u1)(hu2: 0 < u2)(hu3: 0 < u3):
    √u1 + √u2 + √u3 ≤ √(3 * (u1 + u2 + u3)) := by
    have: (√u1*1 + √u2*1 + √u3*1)^2 ≤ (u1+u2+u3) * (1^2+1^2+1^2) := by
      nth_rw 2 [← Real.sq_sqrt (le_of_lt hu1),
      ← Real.sq_sqrt (le_of_lt hu2), ← Real.sq_sqrt (le_of_lt hu3)]
      apply cauchy_schwarz_3
    simp at this; norm_num at this; rw [mul_comm _ 3] at this
    exact Real.le_sqrt_of_sq_le this
  -- apply the above inequality twice, we get
  -- d1 + d2 + d3 ≤ √(6√(3(a+b+c)))
  have h1: d1+d2+d3 ≤ √(6 * √(3*(a+b+c)) ) := by
    rw [d1_def, d2_def, d3_def]
    rw [d1_def, Real.sqrt_pos] at d1_pos
    rw [d2_def, Real.sqrt_pos] at d2_pos
    rw [d3_def, Real.sqrt_pos] at d3_pos
    -- use above cauchy-schwarz inequality
    have h1 := c_s_apply_2 d1_pos d2_pos d3_pos
    -- right side is 6(√a+√b+√c), use the inequality again.
    have: 3*(√b+√c + (√c+√a) + (√a+√b)) = 6 * (√a+√b+√c) := by ring
    rw [this] at h1
    have h2 := c_s_apply_2 ha hb hc
    apply le_trans h1 ?_
    apply Real.sqrt_le_sqrt
    linarith [h2]
  -- thus (a+b+c)^2 / (d1+d2+d3) ≥ (a+b+c)^2 / √(6 √(3(a+b+c)))
  have h2: a^2/d1 + b^2/d2 + c^2/d3 ≥ (a+b+c)^2 / √(6 * √(3*(a+b+c))) := by
    apply le_trans ?_ c_s_apply_1
    apply (div_le_div_iff_of_pos_left ?_ ?_ ?_).mpr h1
    all_goals nlinarith [d1_pos, d2_pos, d3_pos, ha, hb, hc]
  -- thus done. right side of h2 is exactly right side of the desired inequality.
  apply le_trans (le_of_eq ?_) h2
  -- (a+b+c)^(7/4) = (a+b+c)^2 / √(√(a+b+c)), and √(2 √27) = √(6√3)
  have h3: (a+b+c)^(7/4: ℝ) = (a+b+c)^2 / √( √(a+b+c)) := by
    have: 0 ≤ a+b+c := by linarith [ha, hb, hc]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul this,
    ← Real.rpow_natCast, ← Real.rpow_sub (by linarith [ha, hb, hc])]
    congr 1; norm_num
  have h4: √6 * √(√3) = √2 * √(√27) := by
    have: √27 = 3* √3 := by
      have: (27:ℝ) = 3^2 * 3 := by norm_num
      rw [this, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [this, Real.sqrt_mul (by norm_num), ← mul_assoc,
    ← Real.sqrt_mul (by norm_num) 3]; norm_num
  rw [h3]; field_simp
  rw [← h4]; ring