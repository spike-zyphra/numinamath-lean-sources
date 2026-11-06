import Mathlib

/- Man beweise: Für die positiven reellen Zahlen a, b, c gilt die Ungleichung

$$
\frac{a}{\sqrt{(a+b)(a+c)}}+\frac{b}{\sqrt{(b+a)(b+c)}}+\frac{c}{\sqrt{(c+a)(c+b)}} \leq \frac{3}{2} .
$$ -/
theorem inequalities_605934 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / Real.sqrt ((a + b) * (a + c)) + b / Real.sqrt ((b + a) * (b + c)) + c / Real.sqrt ((c + a) * (c + b)) ≤ 3 / 2 := by
  -- Prove the Cauchy-Schwarz inequality.
  have CS_ineq (x₁ y₁ z₁ x₂ y₂ z₂ : ℝ) : (x₁ * x₂ + y₁ * y₂ + z₁ * z₂) ^ 2 ≤ (x₁ ^ 2 + y₁ ^ 2 + z₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2 + z₂ ^ 2) := by
    nlinarith [sq_nonneg (x₁ * y₂ - y₁ * x₂), sq_nonneg (y₁ * z₂ - z₁ * y₂), sq_nonneg (z₁ * x₂ - x₁ * z₂)]
  -- Modify the inequality to (√a * √a / √((a+b)(a+c)) + √b * √b / √((b+a)(b+c)) + √c * √c / √((c+a)(c+b)))² ≤ 9/4.
  nth_rewrite 1 [show a = Real.sqrt a * Real.sqrt a by rw [<-Real.sqrt_mul (le_of_lt ha), Real.sqrt_mul_self (le_of_lt ha)]]
  nth_rewrite 2 [show b = Real.sqrt b * Real.sqrt b by rw [<-Real.sqrt_mul (le_of_lt hb), Real.sqrt_mul_self (le_of_lt hb)]]
  nth_rewrite 3 [show c = Real.sqrt c * Real.sqrt c by rw [<-Real.sqrt_mul (le_of_lt hc), Real.sqrt_mul_self (le_of_lt hc)]]
  rw [mul_div_assoc, mul_div_assoc, mul_div_assoc, <-sq_le_sq₀ (by positivity) (by norm_num)]
  -- Return to the goal and apply Cauchy-Schwarz inequality.
  calc
    (√a * (√a / √((a + b) * (a + c))) + √b * (√b / √((b + a) * (b + c))) + √c * (√c / √((c + a) * (c + b)))) ^ 2
    _ ≤ (√a ^ 2 + √b ^ 2 + √c ^ 2) * ((√a / √((a + b) * (a + c))) ^ 2 + (√b / √((b + a) * (b + c))) ^ 2 + (√c / √((c + a) * (c + b))) ^ 2) := CS_ineq (Real.sqrt a) (Real.sqrt b) (Real.sqrt c) (Real.sqrt a / Real.sqrt ((a + b) * (a + c))) (Real.sqrt b / Real.sqrt ((b + a) * (b + c))) (Real.sqrt c / Real.sqrt ((c + a) * (c + b)))
    _ = (2 * (a * b + b * c + c * a) * (a + b + c)) / ((a + b) * (b + c) * (c + a)) := by
      -- Simplify the expression after apply Cauchy-Schwarz inequality.
      rw [div_pow, div_pow, div_pow]
      -- Clear the square roots and simplify the expression.
      iterate 6 rw [Real.sq_sqrt (by positivity)]
      field_simp
      ring
    _ ≤ (3 / 2) ^ 2 := by
      -- Note that (a + b)(b + c)(c + a) = (a + b + c)(ab + bc + ca) - abc, so the last step is equivalent to (a + b + c)(ab + bc + ca) ≥ 9abc.
      norm_num
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      suffices (a + b + c) * (a * b + b * c + c * a) ≥ 9 * a * b * c by
        linarith only [this]
      -- Prove the AM-GM inequality for three variables.
      have h₁ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / 3 : ℝ) * x + (1 / 3 : ℝ) * y + (1 / 3 : ℝ) * z ≥ x ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ) * z ^ (1 / 3 : ℝ) := by
        apply Real.geom_mean_le_arith_mean3_weighted (by norm_num) (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity) (by norm_num)
      -- Apply the AM-GM inequality for three variables twice.
      have h₂ : a + b + c ≥ 3 * (a * b * c) ^ (1 / 3 : ℝ) := by
        suffices (1 / 3 : ℝ) * (a + b + c) ≥ (a * b * c) ^ (1 / 3 : ℝ) by
          linarith only [this]
        rw [mul_add, mul_add, Real.mul_rpow, Real.mul_rpow]
        apply h₁ a b c
        all_goals
          positivity
      have h₃ : a * b + b * c + c * a ≥ 3 * (a * b * c) ^ (2 / 3 : ℝ) := by
        suffices (1 / 3 : ℝ) * (a * b + b * c + c * a) ≥ (a * b * c) ^ (2 / 3 : ℝ) by
          linarith only [this]
        rw [mul_add, mul_add, show (2 / 3 : ℝ) = 2 * (1 / 3) by norm_num, Real.rpow_mul, show (2 : ℝ) = (2 : ℕ) by simp, Real.rpow_natCast, pow_two, show a * b * c * (a * b * c) = (a * b) * (b * c) * (c * a) by ring, Real.mul_rpow, Real.mul_rpow]
        apply h₁ (a * b) (b * c) (c * a)
        all_goals
          positivity
      -- Multiply the two inequalities together.
      calc
        (a + b + c) * (a * b + b * c + c * a)
        _ ≥ 3 * (a * b * c) ^ (1 / 3 : ℝ) * (3 * (a * b * c) ^ (2 / 3 : ℝ)) := by
          -- Use the two inequalities proved before.
          apply mul_le_mul
          exact h₂
          exact h₃
          positivity
          positivity
        _ = 9 * a * b * c := by
          -- Simplify the expression.
          rw [mul_assoc, mul_assoc, mul_comm, mul_comm 3, mul_assoc, mul_assoc, <-mul_assoc _ _ (3 * 3), <-mul_assoc a b c, <-Real.rpow_add (by positivity)]
          norm_num
          ac_rfl
