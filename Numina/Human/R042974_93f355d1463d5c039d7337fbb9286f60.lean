import Mathlib

/- Let $a, b, c$ be positive real numbers such that $a b c=1$. Prove that

$$
\frac{1}{a \sqrt{c^{2}+1}}+\frac{1}{b \sqrt{a^{2}+1}}+\frac{1}{c \sqrt{b^{2}+1}}>2 .
$$ -/
theorem inequalities_604157 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) :
    2 < 1 / (a * Real.sqrt (c ^ 2 + 1)) + 1 / (b * Real.sqrt (a ^ 2 + 1)) + 1 / (c * Real.sqrt (b ^ 2 + 1)) := by
  -- Define (x, y, z) such that a = x / y, b = y / z, c = z / x.
  let x := a
  let y : ℝ := 1
  let z := 1 / b
  have hxyz : a = x / y ∧ b = y / z ∧ c = z / x := by
    simp [x, y, z, habc]
    rw [eq_div_iff ha.ne', inv_eq_one_div, eq_div_iff hb.ne', <-habc]
    ac_rfl
  -- Prove that x, y, z are positive.
  have hxyz_pos : 0 < x ∧ 0 < y ∧ 0 < z := by
    simp [x, y, z, ha, hb]
  -- Substitute x, y, z into the goal.
  rw [hxyz.1, hxyz.2.1, hxyz.2.2]
  -- Simplify the goal by eliminating the denominators.
  have h₀ : 1 / (√(x ^ 2) / y * √((z / x) ^ 2 + 1)) + 1 / (√(y ^ 2) / z * √((x / y) ^ 2 + 1)) + 1 / (√(z ^ 2) / x * √((y / z) ^ 2 + 1)) = y / √(z ^ 2 + x ^ 2) + z / √(x ^ 2 + y ^ 2) + x / √(y ^ 2 + z ^ 2) := by
    congrm ?_ + ?_ + ?_
    all_goals
      rw [mul_comm, <-mul_div_assoc, one_div_div, <-Real.sqrt_mul (by positivity), add_mul, <-mul_pow, div_mul_cancel₀ _ (by positivity), one_mul]
  nth_rewrite 1 [show x = √(x ^ 2) by rw [Real.sqrt_sq (by positivity)]]
  nth_rewrite 2 [show y = √(y ^ 2) by rw [Real.sqrt_sq (by positivity)]]
  nth_rewrite 3 [show z = √(z ^ 2) by rw [Real.sqrt_sq (by positivity)]]
  rw [h₀]
  -- Prove a small lemma that 2 * (y² / (x² + y² + z²)) ≤ y / √(z² + x²).
  have h₁ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 2 * (y ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2)) ≤ y / √(z ^ 2 + x ^ 2) := by
    rw [<-mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity), show 2 * y ^ 2 = y * (2 * y) by ring, mul_assoc, mul_le_mul_left (by positivity)]
    -- Not it suffices to show that 2 * y * √(z² + x²) ≤ x² + y² + z², this is basically AM-GM inequality of two variables.
    rw [<-sq_le_sq₀ (by positivity) (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
    linarith only [sq_nonneg (y ^ 2 - (z ^ 2 + x ^ 2))]
  -- Now the goal is to prove that 2 < y / √(z² + x²) + z / √(x² + y²) + x / √(y² + z²).
  apply lt_of_le_of_ne
  . -- First prove that 2 ≤ y / √(z² + x²) + z / √(x² + y²) + x / √(y² + z²).
    calc
      2 = 2 * (y ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2)) + 2 * (z ^ 2 / (y ^ 2 + z ^ 2 + x ^ 2)) + 2 * (x ^ 2 / (z ^ 2 + x ^ 2 + y ^ 2)) := by
        field_simp [show 0 < x ^ 2 + y ^ 2 + z ^ 2 by positivity]
        ring
      _ ≤ y / √(z ^ 2 + x ^ 2) + z / √(x ^ 2 + y ^ 2) + x / √(y ^ 2 + z ^ 2) := by
        apply add_le_add
        apply add_le_add
        apply h₁ x y z hxyz_pos.1 hxyz_pos.2.1 hxyz_pos.2.2
        apply h₁ y z x hxyz_pos.2.1 hxyz_pos.2.2 hxyz_pos.1
        apply h₁ z x y hxyz_pos.2.2 hxyz_pos.1 hxyz_pos.2.1
  . -- Now prove that 2 ≠ y / √(z² + x²) + z / √(x² + y²) + x / √(y² + z²).
    by_contra! h₂
    -- Assume on the contrary that 2 = y / √(z² + x²) + z / √(x² + y²) + x / √(y² + z²), then we can derive three equality.
    rw [show 2 = 2 * (y ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2)) + 2 * (z ^ 2 / (y ^ 2 + z ^ 2 + x ^ 2)) + 2 * (x ^ 2 / (z ^ 2 + x ^ 2 + y ^ 2)) by field_simp [show 0 < x ^ 2 + y ^ 2 + z ^ 2 by positivity]; ring] at h₂
    have g₁ : 2 * (y ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2)) = y / √(z ^ 2 + x ^ 2) := by
      linarith only [h₁ x y z hxyz_pos.1 hxyz_pos.2.1 hxyz_pos.2.2, h₁ y z x hxyz_pos.2.1 hxyz_pos.2.2 hxyz_pos.1, h₁ z x y hxyz_pos.2.2 hxyz_pos.1 hxyz_pos.2.1, h₂]
    have g₂ : 2 * (z ^ 2 / (y ^ 2 + z ^ 2 + x ^ 2)) = z / √(x ^ 2 + y ^ 2) := by
      linarith only [h₁ x y z hxyz_pos.1 hxyz_pos.2.1 hxyz_pos.2.2, h₁ y z x hxyz_pos.2.1 hxyz_pos.2.2 hxyz_pos.1, h₁ z x y hxyz_pos.2.2 hxyz_pos.1 hxyz_pos.2.1, h₂]
    have g₃ : 2 * (x ^ 2 / (z ^ 2 + x ^ 2 + y ^ 2)) = x / √(y ^ 2 + z ^ 2) := by
      linarith only [h₁ x y z hxyz_pos.1 hxyz_pos.2.1 hxyz_pos.2.2, h₁ y z x hxyz_pos.2.1 hxyz_pos.2.2 hxyz_pos.1, h₁ z x y hxyz_pos.2.2 hxyz_pos.1 hxyz_pos.2.1, h₂]
    -- Now we have three equalities g₁, g₂, g₃, then we can derive that y² = x² + z², z² = y² + x², x² = z² + y².
    have g₄ : y ^ 2 = x ^ 2 + z ^ 2 := by
      rw [<-mul_div_assoc, div_eq_div_iff (by positivity) (by positivity), show 2 * y ^ 2 = y * (2 * y) by ring, mul_assoc, mul_right_inj' (by positivity)] at g₁
      rw [<-sq_eq_sq₀ (by positivity) (by positivity), mul_pow, Real.sq_sqrt (by positivity)] at g₁
      nlinarith only [sq_nonneg (y ^ 2 - (z ^ 2 + x ^ 2)), g₁]
    have g₅ : z ^ 2 = y ^ 2 + x ^ 2 := by
      rw [<-mul_div_assoc, div_eq_div_iff (by positivity) (by positivity), show 2 * z ^ 2 = z * (2 * z) by ring, mul_assoc, mul_right_inj' (by positivity)] at g₂
      rw [<-sq_eq_sq₀ (by positivity) (by positivity), mul_pow, Real.sq_sqrt (by positivity)] at g₂
      nlinarith only [sq_nonneg (z ^ 2 - (y ^ 2 + x ^ 2)), g₂]
    have g₆ : x ^ 2 = z ^ 2 + y ^ 2 := by
      rw [<-mul_div_assoc, div_eq_div_iff (by positivity) (by positivity), show 2 * x ^ 2 = x * (2 * x) by ring, mul_assoc, mul_right_inj' (by positivity)] at g₃
      rw [<-sq_eq_sq₀ (by positivity) (by positivity), mul_pow, Real.sq_sqrt (by positivity)] at g₃
      nlinarith only [sq_nonneg (x ^ 2 - (z ^ 2 + y ^ 2)), g₃]
    -- It is impossible because x, y, z are positive.
    linarith only [g₄, g₅, g₆, show 0 < x ^ 2 + y ^ 2 + z ^ 2 by positivity]
