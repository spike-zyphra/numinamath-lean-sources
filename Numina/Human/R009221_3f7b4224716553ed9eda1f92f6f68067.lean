import Mathlib

/- Zij $m$ een positief geheel getal. Bewijs dat voor alle positieve reële getallen $a$ en $b$ geldt:

$$
\left(1+\frac{a}{b}\right)^{m}+\left(1+\frac{b}{a}\right)^{m} \geq 2^{m+1}
$$ -/
theorem inequalities_606131 (m : ℕ) (_ : 0 < m) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (1 + a / b) ^ m + (1 + b / a) ^ m ≥ 2 ^ (m + 1) := by 
    have l1 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 2 * √(a * b) ≤ a + b := by
      convert two_mul_le_add_sq √a √b using 1
      . rw [Real.sqrt_mul ha, mul_assoc]
      rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
    -- Apply the inequality of the arithmetic and geometric means to 1 and $\frac{a}{b}$:
    -- $$ 1+\frac{a}{b} \geq 2 \sqrt{\frac{a}{b}} $$
    -- so
    -- $$ \left(1+\frac{a}{b}\right)^{m} \geq\left(2 \sqrt{\frac{a}{b}}\right)^{m} $$
    have h1 : (2 * √(a / b) )^m ≤ (1 + a / b)^m := by 
      have := l1 (show 0 ≤ 1 by simp) (show 0 ≤ a / b by positivity)
      simp at this
      exact pow_le_pow_left₀ (by positivity)  this m 
    -- Similarly, of course,

    -- $$ \left(1+\frac{b}{a}\right)^{m} \geq\left(2 \sqrt{\frac{b}{a}}\right)^{m} $$
    have h2 : (2 * √ (b / a))^m ≤ (1 + b / a)^m := by 
      have := l1 (show 0 ≤ 1 by simp) (show 0 ≤ b / a by positivity) 
      simp at this 
      exact pow_le_pow_left₀ (by positivity)  this m 
    -- Now we apply the inequality of the arithmetic and geometric means again:
    -- $$ \left(2 \sqrt{\frac{a}{b}}\right)^{m}+\left(2 \sqrt{\frac{b}{a}}\right)^{m} \geq 2 \sqrt{\left(2 \sqrt{\frac{a}{b}}\right)^{m} \cdot\left(2 \sqrt{\frac{b}{a}}\right)^{m}}=2^{m+1} $$
    -- This proves the desired result.
    calc 
     _ ≥ (2 * √(a / b)) ^ m  + (2 * √(b / a)) ^ m := add_le_add h1 h2 
     _ ≥ 2 * √ ((2 * √(a / b)) ^ m * (2 * √(b / a)) ^ m) := l1 (by positivity) (by positivity)
     _ = _ := by 
      simp [←mul_pow]
      have h3 : (2 * √(a / b) * (2 * √(b / a)))  = 4 * ( √((a / b) * (b / a)) ):= by 
        rw [Real.sqrt_mul (by positivity)]
        linarith
      simp [h3]
      rw [show a / b  * (b / a) = 1 by field_simp, pow_add ]
      norm_num
      suffices √(4 ^ m) = 2 ^ m by linarith 
      rw [show (4 : ℝ)^m = (2^m)^2 by rw [←pow_mul, mul_comm, pow_mul]; norm_num, Real.sqrt_sq (by positivity)]
  