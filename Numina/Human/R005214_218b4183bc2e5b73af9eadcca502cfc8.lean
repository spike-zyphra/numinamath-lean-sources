import Mathlib

open Real

/- Let $a, b, c, d$ be positive real numbers such that $a b c d=1$. Prove the inequality

$$
\frac{1}{\sqrt{a+2 b+3 c+10}}+\frac{1}{\sqrt{b+2 c+3 d+10}}+\frac{1}{\sqrt{c+2 d+3 a+10}}+\frac{1}{\sqrt{d+2 a+3 b+10}} \leq 1 .
$$ -/
theorem inequalities_606309 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (h : a * b * c * d = 1) :
    1 / sqrt (a + 2 * b + 3 * c + 10) + 1 / sqrt (b + 2 * c + 3 * d + 10) +
    1 / sqrt (c + 2 * d + 3 * a + 10) + 1 / sqrt (d + 2 * a + 3 * b + 10) ≤ 1 := by
  -- Let $x, y, z, t$ be positive numbers such that $a=x^{4}, b=y^{4}, c=z^{4}, d=t^{4}$.
  let x := Real.sqrt (Real.sqrt a)
  let y := Real.sqrt (Real.sqrt b)
  let z := Real.sqrt (Real.sqrt c)
  let t := Real.sqrt (Real.sqrt d)
  -- Rewrite (a, b, c, d) in terms of (x, y, z, t).
  have hx : a = x ^ 4 := by
    simp only [x]
    rw [show 4 = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt, Real.sq_sqrt]
    all_goals
      positivity
  have hy : b = y ^ 4 := by
    simp only [y]
    rw [show 4 = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt, Real.sq_sqrt]
    all_goals
      positivity
  have hz : c = z ^ 4 := by
    simp only [z]
    rw [show 4 = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt, Real.sq_sqrt]
    all_goals
      positivity
  have ht : d = t ^ 4 := by
    simp only [t]
    rw [show 4 = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt, Real.sq_sqrt]
    all_goals
      positivity
  -- Show that x, y, z, t > 0.
  have hx' : 0 < x := by
    simp [x]
    positivity
  have hy' : 0 < y := by
    simp [y]
    positivity
  have hz' : 0 < z := by
    simp [z]
    positivity
  have ht' : 0 < t := by
    simp [t]
    positivity
  clear_value x y z t
  -- Rewrite h.
  rw [hx, hy, hz, ht] at h
  -- Prove AM-GM inequality for two variables.
  have amgm₂ (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 2 * Real.sqrt (x * y) ≤ x + y := by
    -- Show that $2 \sqrt{x y} \leq x+y$.
    apply le_of_sq_le_sq
    rw [mul_pow, Real.sq_sqrt]
    linarith only [sq_nonneg (x - y)]
    positivity
    positivity
  -- Prove AM-GM inequality for four variables.
  have amgm₄ (x y z t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) : x ^ 4 + y ^ 4 + z ^ 4 + t ^ 4 ≥ 4 * x * y * z * t := by
    calc
      x ^ 4 + y ^ 4 + z ^ 4 + t ^ 4 = x ^ 4 + y ^ 4 + (z ^ 4 + t ^ 4) := by
        ac_rfl
      _ ≥ 2 * (x ^ 2) * (y ^ 2) + 2 * (z ^ 2) * (t ^ 2) := by
        -- Use the AM-GM inequality for two variables.
        apply add_le_add
        nlinarith only [sq_nonneg (x ^ 2 - y ^ 2)]
        nlinarith only [sq_nonneg (z ^ 2 - t ^ 2)]
      _ = 2 * ((x * y) ^ 2 + (z * t) ^ 2) := by
        ring_nf
      _ ≥ 2 * (2 * (x * y) * (z * t)) := by
        -- Use the AM-GM inequality for two variables.
        apply mul_le_mul (by rfl)
        nlinarith only [sq_nonneg (x * y - z * t)]
        positivity
        norm_num
      _ = 4 * x * y * z * t := by
        ring_nf
  -- Prove the lemma x ^ 4 + 2 * y ^ 4 + 3 * z ^ 4 + 10 ≥ 4 * (x * y * z + y * z + z + 1).
  have lemma₁ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ 4 + 2 * y ^ 4 + 3 * z ^ 4 + 10 ≥ 4 * (x * y * z + y * z + z + 1) := by
    -- Show that $x^{4}+y^{4}+z^{4}+1 \geq 4 x y z$.
    have h₁ := amgm₄ x y z 1 hx hy hz (by norm_num)
    -- Show that $y^{4}+z^{4}+1+1 \geq 4 y z$.
    have h₂ := amgm₄ y z 1 1 hy hz (by norm_num) (by norm_num)
    -- Show that $z^{4}+1+1+1 \geq 4 z$.
    have h₃ := amgm₄ z 1 1 1 hz (by norm_num) (by norm_num) (by norm_num)
    -- Use linarith to add the inequalities to get the desired result.
    linarith only [h₁, h₂, h₃]
  -- Prove that x * y * z * t = 1.
  rw [<-mul_pow, <-mul_pow, <-mul_pow, show (1 : ℝ) = 1 ^ 4 by norm_num] at h
  rw [pow_left_inj₀ (by positivity) (by positivity) (by norm_num)] at h
  -- Return to the main inequality.
  calc
    1 / Real.sqrt (a + 2 * b + 3 * c + 10) + 1 / Real.sqrt (b + 2 * c + 3 * d + 10) + 1 / Real.sqrt (c + 2 * d + 3 * a + 10) + 1 / Real.sqrt (d + 2 * a + 3 * b + 10)
    _ = 1 / Real.sqrt (x ^ 4 + 2 * y ^ 4 + 3 * z ^ 4 + 10) + 1 / Real.sqrt (y ^ 4 + 2 * z ^ 4 + 3 * t ^ 4 + 10) + 1 / Real.sqrt (z ^ 4 + 2 * t ^ 4 + 3 * x ^ 4 + 10) + 1 / Real.sqrt (t ^ 4 + 2 * x ^ 4 + 3 * y ^ 4 + 10) := by
      rw [hx, hy, hz, ht]
    _ ≤ 1 / (2 * Real.sqrt (x * y * z + y * z + z + 1)) + 1 / (2 * Real.sqrt (y * z * t + z * t + t + 1)) + 1 / (2 * Real.sqrt (z * t * x + t * x + x + 1)) + 1 / (2 * Real.sqrt (t * x * y + x * y + y + 1)) := by
      -- Use lemma₁ to show that $ \frac{1}{\sqrt{x^{4}+2 y^{4}+3 z^{4}+10}} \leq \frac{1}{2√(xyz+yz+z+1)} $, and similar for the other three terms.
      apply add_le_add
      apply add_le_add
      apply add_le_add
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity)
      rw [<-sq_le_sq₀ (by positivity) (by positivity), Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
      norm_num
      apply lemma₁ x y z hx' hy' hz'
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity)
      rw [<-sq_le_sq₀ (by positivity) (by positivity), Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
      norm_num
      apply lemma₁ y z t hy' hz' ht'
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity)
      rw [<-sq_le_sq₀ (by positivity) (by positivity), Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
      norm_num
      apply lemma₁ z t x hz' ht' hx'
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity)
      rw [<-sq_le_sq₀ (by positivity) (by positivity), Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
      norm_num
      apply lemma₁ t x y ht' hx' hy'
    _ = (1 + Real.sqrt (x * y * z) + Real.sqrt (y * z) + Real.sqrt z) / (2 * Real.sqrt (x * y * z + y * z + z + 1)) := by
      -- Combine the four terms into one term, using the fact that x * y * z * t = 1.
      rw [add_div, add_div, add_div]
      congrm ?_ + ?_ + ?_ + ?_
      . -- The first term is identitcal.
        rfl
      . -- Use xyzt = 1 to simplify the second term.
        rw [div_eq_div_iff (by positivity) (by positivity)]
        ring_nf
        rw [mul_left_inj' (by norm_num), <-Real.sqrt_mul (by positivity), mul_add, mul_add, mul_add]
        rw [show x * y * z * (y * z * t) = y * z * (x * y * z * t) by ring, show x * y * z * (z * t) = z * (x * y * z * t) by ring, h, mul_one, mul_one, mul_one]
        ac_rfl
      . -- Use xyzt = 1 to simplify the third term.
        rw [div_eq_div_iff (by positivity) (by positivity)]
        ring_nf
        rw [mul_left_inj' (by norm_num), <-Real.sqrt_mul (by positivity), mul_add, mul_add, mul_add]
        rw [show y * z * (x * z * t) = z * (x * y * z * t) by ring, show y * z * (x * t) = x * y * z * t by ring, h, mul_one, mul_one, mul_comm (y * z) x, <-mul_assoc]
        ac_rfl
      . -- Use xyzt = 1 to simplify the fourth term.
        rw [div_eq_div_iff (by positivity) (by positivity)]
        ring_nf
        rw [mul_left_inj' (by norm_num), <-Real.sqrt_mul (by positivity), mul_add, mul_add, mul_add]
        rw [show z * (x * y * t) = x * y * z * t by ring, h, mul_one, mul_comm z (x * y), mul_comm z y]
        ac_rfl
    _ ≤ 1 := by
      -- Finally prove that 1 + √(xyz) + √(yz) + √z ≤ 2√(xyz+yz+z+1), so that the inequality holds.
      rw [div_le_iff₀]
      -- Simplify the expression.
      simp
      rw [<-sq_le_sq₀, mul_pow, Real.sq_sqrt, add_sq, add_sq, add_sq, Real.sq_sqrt, mul_assoc 2 (1 + Real.sqrt (x * y * z)), add_mul, <-Real.sqrt_mul, Real.sq_sqrt, mul_assoc 2 _ (Real.sqrt z), add_mul, add_mul, <-Real.sqrt_mul, <-Real.sqrt_mul, Real.sq_sqrt]
      -- Use AM-GM inequality of two variables for 6 times.
      have h₁ := amgm₂ (x * y * z) (y * z) (by positivity) (by positivity)
      have h₂ := amgm₂ (x * y * z) z (by positivity) hz'
      have h₃ := amgm₂ (x * y * z) 1 (by positivity) (by norm_num)
      rw [mul_one] at h₃
      have h₄ := amgm₂ (y * z) z (by positivity) hz'
      have h₅ := amgm₂ (y * z) 1 (by positivity) (by norm_num)
      rw [mul_one] at h₅
      have h₆ := amgm₂ z 1 (by positivity) (by norm_num)
      rw [mul_one] at h₆
      -- Combine the inequalities to get the desired result.
      linarith only [h₁, h₂, h₃, h₄, h₅, h₆]
      -- Clear remaining goals.
      all_goals
        positivity
