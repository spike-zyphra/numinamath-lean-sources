import Mathlib

/- Given positive real numbers $a, b, c, d$ that satisfy equalities


$$

a^{2}+d^{2}-a d=b^{2}+c^{2}+b c \quad \text { and } \quad a^{2}+b^{2}=c^{2}+d^{2}

$$


find all possible values of the expression $\frac{a b+c d}{a d+b c}$.

Answer: $\frac{\sqrt{3}}{2}$. -/
theorem algebra_238097 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a^2 + d^2 - a * d = b^2 + c^2 + b * c) (h2 : a^2 + b^2 = c^2 + d^2) :
    (a * b + c * d) / (a * d + b * c) = Real.sqrt 3 / 2 := by
  -- let's first show the numerator is positive
  have h3 : 0 < a * d + b * c:= by positivity
  -- from h1 and h2 we can estimate the numerator
  have h4 : (a * b + c * d) ^ 2 = 3 / 4 * (a * d + b * c) ^ 2:= by
    nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a * c - b * d), sq_nonneg (a * d - b * c), sq_nonneg (a * b - c * d), h1, h2]
  have h5 : a * b + c * d = Real.sqrt 3 / 2 * (a * d + b * c):= by
    apply congr_arg (fun t => √t) at h4
    rw [Real.sqrt_sq (by positivity), Real.sqrt_mul, Real.sqrt_sq (by positivity), Real.sqrt_div (by norm_num), show (4:ℝ)=2^2 by norm_num, Real.sqrt_sq (by norm_num)] at h4
    exact h4; norm_num
  -- now we just simplify to finish
  rw [h5]
  field_simp
  nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0)]