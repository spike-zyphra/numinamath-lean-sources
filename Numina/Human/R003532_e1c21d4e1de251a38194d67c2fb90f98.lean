import Mathlib

open Real

/- 23. Given that $a, b, c$ are positive numbers satisfying $a^{2}=b^{2}+c^{2}$. Prove:

$$

a^{3}+b^{3}+c^{3} \geqslant \frac{2 \sqrt{2}+1}{7}\left[a^{2}(b+c)+b^{2}(c+a)+c^{2}(a+b)\right] .

$$
 -/
theorem inequalities_192489 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 = b^2 + c^2) :
    a^3 + b^3 + c^3 ≥ ((2 * sqrt 2 + 1) / 7) * (a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b)) := by

  -- we'll need two variable amgm so let's show that first
  -- have h_amgm : ∀ x y : ℝ, 0 < x → 0 < y → 2*√(x*y) ≤ x+y := by
  --   intro x y hx hy
  --   refine (sq_le_sq₀ ?_ ?_).mp ?_
  --   positivity
  --   positivity
  --   rw [mul_pow, Real.sq_sqrt (by positivity)]; ring_nf
  --   nlinarith [sq_nonneg (y-x)]
  -- first use am-gm
  have h0g: ∀ b c:ℝ, 0 < b → 0 < c →b^3+c^3 ≥ b^2*c+b*c^2 := by
    intro b c hb hc
    have h0: b^3+b*c^2+c^3+b^2*c ≥ 2*b^2*c+2*b*c^2 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b - c + 2 * c), sq_nonneg (b + c - 2 * c)]
    linarith
  -- we can do the same theory for a and √2*b
  have h0 := h0g b c hb hc
  have h1 := h0g a (√2*b) ha (by positivity)
  have h1: √2 * (a ^ 3 + (√2 * b) ^ 3) ≥ √2 * (a ^ 2 * (√2 * b) + a * (√2 * b) ^ 2) := by nlinarith [Real.sqrt_nonneg 2]
  rw [mul_add, mul_pow, mul_pow, mul_add, show √2^3=(√2)^2*√2 by ring_nf, Real.sq_sqrt (by positivity), show √2 * (2 * √2 * b ^ 3) = √2^2 * 2 * b ^ 3 by ring_nf, Real.sq_sqrt (by positivity),
      show 2 * 2 * b ^ 3 = 4*b^3 by ring_nf, show √2 * (a * (2 * b ^ 2)) = 2 * √2 * a * b ^ 2 by ring_nf, show √2 * (a ^ 2 * (√2 * b)) = √2^2*a^2*b by ring_nf, Real.sq_sqrt (by positivity)
  ] at h1
  -- repeat for a and √2*c
  have h2 := h0g a (√2*c) ha (by positivity)
  have h2: √2 * (a ^ 3 + (√2 * c) ^ 3) ≥ √2 * (a ^ 2 * (√2 * c) + a * (√2 * c) ^ 2) := by nlinarith [Real.sqrt_nonneg 2]
  rw [mul_add, mul_pow, mul_pow, mul_add, show √2^3=(√2)^2*√2 by ring_nf, Real.sq_sqrt (by positivity), show √2 * (2 * √2 * c ^ 3) = √2^2 * 2 * c ^ 3 by ring_nf, Real.sq_sqrt (by positivity),
      show 2 * 2 * c ^ 3 = 4*c^3 by ring_nf, show √2 * (a * (2 * c ^ 2)) = 2 * √2 * a * c ^ 2 by ring_nf, show √2 * (a ^ 2 * (√2 * c)) = √2^2*a^2*c by ring_nf, Real.sq_sqrt (by positivity)
  ] at h2
  -- we can add 3*h0 + h1 + h2
  have h3 : 3*(b^3+c^3) + ( √2 * a ^ 3 + 4 * b ^ 3 ) + (√2 * a ^ 3 + 4 * c ^ 3) ≥ 3*(b ^ 2 * c + b * c ^ 2) + (2 * a ^ 2 * b + 2 * √2 * a * b ^ 2) + (2 * a ^ 2 * c + 2 * √2 * a * c ^ 2) := by linarith
  rw [show 3 * (b ^ 3 + c ^ 3) + (√2 * a ^ 3 + 4 * b ^ 3) + (√2 * a ^ 3 + 4 * c ^ 3) = 2*√2*a^3+7*b^3+7*c^3 by ring_nf,
      show 3 * (b ^ 2 * c + b * c ^ 2) + (2 * a ^ 2 * b + 2 * √2 * a * b ^ 2) + (2 * a ^ 2 * c + 2 * √2 * a * c ^ 2) = 2*a^2*(b+c) + 2*√2*(b^2*a+c^2*a) + 3 * (b^2*c+c^2*b) by ring_nf
  ] at h3
  have h4: a ≥ (b+c)/√2 := by
    have h4a: a^2 ≥ (b+c)^2/2 := by
      rw [h]; nlinarith [sq_nonneg (b - c)]
    simp at h4a ⊢
    apply (sq_le_sq₀ ?_ ?_).mp
    rotate_left; positivity; linarith
    rw [div_pow, Real.sq_sqrt (by positivity)]; linarith
  -- we can now show that (5-√2)*a^3 ≥ (2*√2-1)a^2*(b+c)+b^2a+c^2a
  have h5: (5 - √2) * a ^ 3 ≥ (2 * √2 - 1) * a ^ 2 * (b + c) + b ^ 2 * a + c ^ 2 * a := by
    rw [show (5 - √2) * a ^ 3 = (4 - √2) * a ^ 3 + a ^ 3 by ring_nf]
    have h5a: (4 - √2) * a ^ 3 ≥ ((4 - √2) * a ^ 2) * ((b+c)/√2) := by
      have h5b: (4 - √2) * a ^ 3 = ((4 - √2) * a ^ 2) * a := by ring_nf
      rw [h5b]
      gcongr
      apply mul_nonneg
      simp; refine (sqrt_le_left ?_).mpr ?_; norm_num; norm_num
      nlinarith
    have h5b:(4 - √2) * a ^ 3 + a^3 ≥ ((4 - √2) * a ^ 2) * ((b+c)/√2) + a^3 := by linarith
    rw(config := { occs := .pos [3]})  [show a^3=b^2*a+c^2*a by rw [show a^3=a^2*a by ring_nf, h, add_mul]] at h5b
    suffices (4 - √2) * a ^ 2 * ((b + c) / √2) + (b ^ 2 * a + c ^ 2 * a) = (2 * √2 - 1) * a ^ 2 * (b + c) + b ^ 2 * a + c ^ 2 * a by
      rw [← this]; assumption
    rw [← add_assoc]; simp
    rw [mul_div, show (4 - √2) * a ^ 2 * (b + c) / √2 = ((4 - √2)/√2) * a ^ 2 * (b + c) by ring_nf]
    simp; left; left; field_simp; ring_nf; rw [Real.sq_sqrt (by positivity)]; ring_nf
  have h6:(2-√2)*a^3≥(2*√2-2)*(b^2*c+c^2*b) := by
    have h6a: a^3 ≥ √2 * (b^2 * c + c^2 * b) := by
      calc a^3
      _ = a^2*a := by ring_nf
      _ ≥ a^2 * ((b + c) / √2) := by gcongr
      _ = (b^2+c^2) * (b+c)/√2 := by rw [h]; ring_nf
      _ ≥ (2*b*c) * (b+c)/√2 := by gcongr; nlinarith [sq_nonneg (b - c)]
      _ = (2/√2) * (b^2*c+c^2*b) := by ring_nf
      _ = √2 * (b^2*c+c^2*b) := by simp
    have h6b: (2-√2)*a^3 ≥ (2-√2)*(√2 * (b^2 * c + c^2 * b)) := by
      gcongr
      simp; refine (sqrt_le_left ?_).mpr ?_
      norm_num; norm_num
    suffices (2 - √2) * (√2 * (b ^ 2 * c + c ^ 2 * b)) = (2 * √2 - 2) * (b ^ 2 * c + c ^ 2 * b) by rw [← this]; assumption
    ring_nf; simp
    norm_cast; ring_nf
  -- we can add the obtained equations to solve the problem
  linarith