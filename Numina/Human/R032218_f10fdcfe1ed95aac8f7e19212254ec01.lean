import Mathlib

open Real Set

/- Example 15 (16th Irish Mathematical Olympiad) Let $a, b>0$, find the largest positive number $c$, such that for any positive real number $x$, we have $c \leqslant \max \left\{a x+\frac{1}{a x}, b x+\frac{1}{b x}\right\}$. -/
theorem inequalities_162237 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsGreatest {c : ℝ | 0 < c ∧ ∀ x > 0, c ≤ max (a * x + 1 / (a * x)) (b * x + 1 / (b * x)) }
    (√ (b / a) + √ (a / b)) := by
  constructor
  -- first proveing √(b / a) + √(a / b) belongs to set
  . simp [-le_sup_iff]
    and_intros
    . positivity
    . rintro x hx
      calc
        -- first prove that the expression is less than following expression by using amgm for 2 variables
        _ ≤ (1/2 * b * x + 1/2 * x⁻¹ * a⁻¹) + (1/2 * a * x + 1/2 * x⁻¹ * b⁻¹) := by
          -- as similar argumetn for two terms, prove a common lemma
          have (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr: 0 < r) : √(p / q) ≤ 1 / 2 * p * r + 1 / 2 * r⁻¹ * q⁻¹ := by
            have : (0 : ℝ) ≤ 1/2 := by norm_num
            convert geom_mean_le_arith_mean2_weighted this this (show 0 ≤ p * r by positivity) (show 0 ≤ r⁻¹  * q⁻¹ by positivity) (by norm_num) using 1
            . rw [← mul_rpow (by positivity) (by positivity), sqrt_eq_rpow]
              congr
              field_simp
              ring
            . ring
          gcongr
          . apply this b a x hb ha hx
          . apply this a b x ha hb hx
        -- now write the expression as mean of two arguments of max
        _ = ((a * x + x⁻¹ * a⁻¹) + (b * x + x⁻¹ * b⁻¹))/2 := by ring
        -- the mean is less than or equal to max of two arguments
        _ ≤ _ := by
          have := le_max_left (a * x + x⁻¹ * a⁻¹) (b * x + x⁻¹ * b⁻¹)
          have := le_max_right (a * x + x⁻¹ * a⁻¹) (b * x + x⁻¹ * b⁻¹)
          linarith
    -- now proving √ (b / a) + √ (a / b) is a upper bound
  . rintro c ⟨hc, hcx⟩
    -- plug in 1 / (√a * √b) into the expression
    rw [sqrt_div (by positivity), sqrt_div (by positivity)]
    rw [← sq_sqrt (x := a) (by positivity), ← sq_sqrt (x := b) (by positivity)] at hcx
    specialize hcx (1 / (√a * √b)) (by positivity)
    have ha : 0 < √a := by positivity
    have hb : 0 < √b := by positivity
    -- both arguments of max turn to same expression, √ (b / a) + √ (a / b)
    generalize √a = p, √b = q at hcx ha hb
    have : p ^ 2 * (1 / (p * q)) + 1 / (p ^ 2 * (1 / (p * q))) = q / p + p / q := by
      field_simp; ring
    rw [this] at hcx
    have : q ^ 2 * (1 / (p * q)) + 1 / (q ^ 2 * (1 / (p * q))) = q / p + p / q := by
      field_simp; ring
    rw [this] at hcx
    simpa using hcx