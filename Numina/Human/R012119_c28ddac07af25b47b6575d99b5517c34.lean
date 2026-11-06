import Mathlib

open Real Set

/- 8. Given $a, b, c \in R, a^{2}+b^{2}+c^{2}=1$, then the minimum value of $3 a b-3 b c+2 c^{2}$ is $\qquad$

Translate the above text into English, please retain the original text's line breaks and format, and output the translation result directly. -/
theorem other_184663:
    IsLeast {x | ∃ a b c : ℝ, a^2 + b^2 + c^2 = 1 ∧ x = 3 * a * b - 3 * b * c + 2 * c^2} (- (1 + sqrt 7) / 2) := by

  unfold IsLeast lowerBounds; simp
  constructor
  rotate_left
  · -- we first need to show that the inequality holds
    intro lower a b c hsq hlower
    rw [hlower]; clear hlower
    -- We'll use a generalized amgm on two variables
    have hamgm: ∀x y α :ℝ, 0<α → 2*|x*y| ≤ α *x^2 + (1/α) * y^2 := by
      intro x y α hα
      suffices 0 ≤ α * x ^ 2 + 1 / α * y ^ 2 - 2 * |x * y| by linarith
      rw [show α * x ^ 2 + 1 / α * y ^ 2 - 2 * |x * y| = (√α * |x| - 1/√α * |y|)^2 by ring_nf; rw [sq_sqrt (by linarith), show (√α)⁻¹ ^ 2 = (√α)⁻¹ ^ (2:ℝ) by norm_cast,Real.inv_rpow (by exact sqrt_nonneg α),show √α ^ (2:ℝ) = √α ^ (2:ℕ) by norm_cast,sq_sqrt (by linarith), show √α * |x| * (√α)⁻¹ * |y| * 2 = 2 * |x| * |y| * (√α * (√α)⁻¹) by ring_nf, mul_inv_cancel₀ (by exact sqrt_ne_zero'.mpr hα),mul_one]; ring_nf; rw [sq_abs, sq_abs, abs_mul]]
      nlinarith
    -- with this, we can create a bound on 3ab-3bc+2c^2
    have h2:∀ m n:ℝ, m>0 → n>0 → 3*a*b-3*b*c+2*c^2 ≥ (-3*m/2)*a^2 +(-3/(2*m)-3*n/2)*b^2+(-3/(2*n)+2)*c^2 := by
      intro m n hm hn
      calc 3*a*b-3*b*c+2*c^2
      _ = 3/2*(2*a*b)+(-3/2*(2*b*c))+2*c^2 := by ring_nf
      _ ≥ -3/2 *(m*a^2+1/m*b^2)+(-3/2*(n*b^2+1/n*c^2))+2*c^2 := by
        apply add_le_add ?_ (by simp); apply add_le_add;
        suffices -(m * a ^ 2 + 1 / m * b ^ 2) ≤ 2*a*b by linarith
        apply neg_le.mp
        suffices -a*b ≤ |a*b| by linarith [hamgm a b m hm]
        apply le_abs.mpr (by apply Or.intro_right; simp)
        suffices 2*b*c ≤ n * b ^ 2 + 1 / n * c ^ 2 by linarith
        suffices b*c ≤ |b*c| by linarith [hamgm b c n hn]
        exact le_abs_self (b * c)
      _ = (-3*m/2)*a^2 +(-3/(2*m)-3*n/2)*b^2+(-3/(2*n)+2)*c^2:= by ring_nf
      -- if we make the factors equal each other, we can then then factor out a^2+b^2+c^2=1 and solve the problem
    -- so we need to solve -3m/2=-3/(2*m)-3*n/2=-3/(2*n)+2
    -- this doesn't need to be a formal solution, we obtain by hand m=(1+sqrt(7))/3, n=(5-√7)/6
    -- The factors then all equal -(1+sqrt(7))/2 so 3*a*b-3*b*c+2*c^2 ≥ -(1+sqrt(7))/2
    -- To match that value, we'll later take b=-(1+√7)/2*a, c = (5-√7)/6*b
    specialize h2 ((1+√7)/3) ((5-√7)/6) (by positivity) (by apply div_pos; rotate_left; norm_num; simp; refine (sqrt_lt' ?_).mpr ?_; norm_num; norm_num)
    -- to simplify h2 we'll use aux lemma
    have h3:-3 * ((1 + √7) / 3) / 2 * a ^ 2 + (-3 / (2 * ((1 + √7) / 3)) - 3 * ((5 - √7) / 6) / 2) * b ^ 2 + (-3 / (2 * ((5 - √7) / 6)) + 2) * c ^ 2 = -(1+√(7))/2*(a^2+b^2+c^2) := by
      conv_lhs =>
        calc _
        _ = -((1 + √7) * (3/ 3)) / 2 * a ^ 2 - (3 / (2 * (1 + √7) / 3) + (5 - √7) * ((3/ 3)/2) / 2) * b ^ 2 + (-3 / ((5 - √7) * ((2 / 2) / 3)) + 2) * c ^ 2 := by ring_nf
        _ = -(1 + √7)/2 * a^2 - (3 / (2 * (1 + √7) / 3) + (5 - √7) * (1/2)/2)*b^2 + (-3 / ((5 - √7) * (1/3))+2) * c^2 := by rw [div_self (by norm_num), div_self (by norm_num), mul_one]
        _ = -(1 + √7) / 2 * a ^ 2 - (9 / (2 * (1 + √7)) + (5 - √7) / 4) * b ^ 2 - (9 / (5 - √7) - 2) * c ^ 2 := by rw [← div_mul, mul_div, div_div, mul_div, mul_one, ← div_mul]; ring_nf
        _ = -(1 + √7) / 2 * a ^ 2 - (9 / (2 * (1 + √7)) * ((1-√7)/(1-√7)) + (5 - √7) / 4) * b ^ 2 - (9 / (5 - √7) * ((5+√7)/(5+√7)) - 2) * c ^ 2 := by rw [div_self (by apply ne_of_lt; simp; refine (lt_sqrt ?_).mpr ?_; norm_num; norm_num), div_self (by positivity), mul_one, mul_one]
        _ = -(1 + √7) / 2 * a ^ 2 - (9 * (1 - √7) / (2 * (1 + √7) * (1 - √7)) + (5 - √7) / 4) * b ^ 2 - (9 * (5 + √7) / ((5 - √7) * (5 + √7)) - 2) * c ^ 2 := by rw [div_mul_div_comm, div_mul_div_comm]
        _ = -(1 + √7) / 2 * a ^ 2 - (9 * (1 - √7) / -12 + (5 - √7) / 4) * b ^ 2 - (9 * (5 + √7) / 18 - 2) * c ^ 2 := by rw [mul_assoc 2, show (1 + √7) * (1 - √7)=1-7 by ring_nf; rw [sq_sqrt (by norm_num)]; norm_num, show (5 - √7) * (5 + √7) = 25-7 by ring_nf; rw [sq_sqrt (by norm_num)]; norm_num]; norm_num
        _ = -(1 + √7) / 2 * a ^ 2 - (1+√7)/2 * b^2 - (1+√7)/2 * c^2 := by ring_nf
        _ = -(1 + √7) / 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by ring_nf

    rw [h3, hsq] at h2
    simp at h2; exact h2
  · -- let's use the values to match the lower bound, we need to pick normalized values to make a^2+b^2+c^2=1
    -- we simplify on paper to minimize work inside lean
    use (-2*√7-1)/√(70+14*√7), (5+√7)/√(70+14*√7), 3/√(70+14*√7)
    constructor
    · ring_nf; field_simp; ring_nf
    · ring_nf; field_simp; ring_nf
      rw [show √7^3=√7 * √7^2 by ring_nf, show √7^4=√7^2 * √7^2 by ring_nf, sq_sqrt (by norm_num)]
      ring_nf