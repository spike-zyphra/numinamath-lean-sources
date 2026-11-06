import Mathlib

/- Let $a, b, c$ be real numbers in the interval $[0,1]$ with $a+b, b+c, c+a \geq 1$. Prove that  $$ 1 \leq(1-a)^{2}+(1-b)^{2}+(1-c)^{2}+\frac{2 \sqrt{2} a b c}{\sqrt{a^{2}+b^{2}+c^{2}}} $$ -/
theorem inequalities_604597 (a b c : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) (h1 : 1 ≤ a + b) (h2 : 1 ≤ b + c) (h3 : 1 ≤ c + a) :
    1 ≤ (1 - a) ^ 2 + (1 - b) ^ 2 + (1 - c) ^ 2 + 2 * Real.sqrt 2 * a * b * c / Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
  -- Show that it suffices to show k² ≤ (k - a)² + (k - b)² + (k - c)² + 2√2abc / √(a² + b² + c²) for k = (a + b + c) / 2.
  have hk (k : ℝ) : k = (a + b + c) / 2 → k ^ 2 ≤ (k - a) ^ 2 + (k - b) ^ 2 + (k - c) ^ 2 + 2 * Real.sqrt 2 * a * b * c / Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) → 1 ≤ (1 - a) ^ 2 + (1 - b) ^ 2 + (1 - c) ^ 2 + 2 * Real.sqrt 2 * a * b * c / Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
    intro hk h
    -- We have (k - 1) * (3 * (k + 1) - 2 * (a + b + c)) ≤ (k - 1) * (k + 1) and hence the result.
    linarith only [show (k - 1) * (3 * (k + 1) - 2 * (a + b + c)) ≤ (k - 1) * (k + 1) by simp [hk]; linarith only [sq_nonneg (a + b + c - 2)], h]
  -- Now prove the result by considering k = (a + b + c) / 2 case.
  let k := (a + b + c) / 2
  apply hk k (by rfl)
  -- It remains to show that k² ≤ (k - a)² + (k - b)² + (k - c)² + 2√2abc / √(a² + b² + c²).
  -- Let x = k - a, y = k - b and z = k - c.
  let x := k - a
  let y := k - b
  let z := k - c
  -- Show that x, y, z are non-negative.
  have hx : 0 ≤ x := by
    simp [x, k]
    linarith
  have hy : 0 ≤ y := by
    simp [y, k]
    linarith
  have hz : 0 ≤ z := by
    simp [z, k]
    linarith
  -- Show that x + y + z = k.
  have hxyz : x + y + z = k := by
    simp [x, y, z, k]
    ring
  -- Show that x + y + z > 0.
  have hxyz' : x + y + z > 0 := by
    -- Contradiction is derived if x + y + z = a + b + c = 0.
    by_contra!
    simp [hxyz, k] at this
    linarith only [show a = 0 by linarith, show b = 0 by linarith, h1]
  -- Show that (y + z)² + (z + x)² + (x + y)² > 0.
  have hxyz'' : (y + z) ^ 2 + (z + x) ^ 2 + (x + y) ^ 2 > 0 := by
    -- Contradiction is derived if (y + z)² + (z + x)² + (x + y)² = 0.
    by_contra! h
    have : (y + z) ^ 2 = 0 := by
      linarith [sq_nonneg (y + z), sq_nonneg (z + x), sq_nonneg (x + y)]
    simp at this
    rw [this] at h
    have : (z + x) ^ 2 = 0 := by
      linarith [sq_nonneg (z + x), sq_nonneg (x + y)]
    simp at this
    rw [this] at h
    have : (x + y) ^ 2 = 0 := by
      linarith [sq_nonneg (x + y)]
    simp at this
    linarith
  -- Substitute x, y, z in the goal.
  -- The goal becomes (x + y + z)² ≤ x² + y²+ z² + 2√2(y + z)(z + x)(x + y) / √((y + z)² + (z + x)² + (x + y)²).
  rw [show k - a = x by rfl, show k - b = y by rfl, show k - c = z by rfl, <-hxyz, show a = y + z by ring, show b = z + x by ring, show c = x + y by ring]
  -- Rearrange the terms.
  suffices Real.sqrt ((y + z) ^ 2 + (z + x) ^ 2 + (x + y) ^ 2) * (2 * (x * y + y * z + z * x)) ≤ (2 * Real.sqrt 2 * (y + z) * (z + x) * (x + y)) by
    rw [mul_comm, <-le_div_iff₀] at this
    linarith only [this]
    positivity
  -- Let t = xy + yz + zx.
  let t := x * y + y * z + z * x
  rw [show x * y + y * z + z * x = t by rfl]
  -- Note that (x + y)(x + z) = x² + t, (y + z)(y + x) = y² + t and (z + x)(z + y) = z² + t. So ((y + z) * (z + x) * (x + y))² = (x² + t)(y² + t)(z² + t).
  have ht : ((y + z) * ((z + x) * (x + y))) ^ 2 = (x ^ 2 + t) * (y ^ 2 + t) * (z ^ 2 + t) := by
    ring
  -- Square both sides of the goal and simplify the terms.
  rw [<-sq_le_sq₀, mul_pow, Real.sq_sqrt (by positivity), mul_assoc, mul_assoc, mul_pow (2 * Real.sqrt 2), ht, mul_pow _ (Real.sqrt 2), Real.sq_sqrt (by norm_num)]
  rw [show (y + z) ^ 2 + (z + x) ^ 2 + (x + y) ^ 2 = 2 * (x ^ 2 + y ^ 2 + z ^ 2 + t) by ring, mul_pow, mul_comm (2 ^ 2), <-mul_assoc, mul_comm, <-mul_assoc, <-mul_assoc, mul_assoc]
  rw [mul_le_mul_left]
  -- Now it is obvious upon expansion, there are more terms on the right hand side.
  linarith only [show 0 ≤ x ^ 2 * y ^ 2 * z ^ 2 by positivity, show 0 ≤ x ^ 2 * y ^ 2 * t by positivity, show 0 ≤ y ^ 2 * z ^ 2 * t by positivity, show 0 ≤ x ^ 2 * z ^ 2 * t by positivity]
  all_goals
    positivity

