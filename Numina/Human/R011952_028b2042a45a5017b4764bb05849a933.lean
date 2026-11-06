import Mathlib

/- 5. Find all pairs of positive numbers $(x, y)$ that satisfy the system of equations $\left\{\begin{array}{l}y-2 \sqrt{x y}-\sqrt{\frac{y}{x}}+2=0, \\ 3 x^{2} y^{2}+y^{4}=84 .\end{array}\right.$ -/
theorem algebra_162725 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : y - 2 * Real.sqrt (x * y) - Real.sqrt (y / x) + 2 = 0)
    (h2 : 3 * x ^ 2 * y ^ 2 + y ^ 4 = 84) :
    (x, y) = (1 / 3, 3) ∨ (x, y) = ((21 / 76) ^ ((1 : ℝ) / 4), 2 * (84 / 19) ^ ((1 : ℝ) / 4)) := by
  simp
  -- let u = √(y/x) and v=√(x*y), both clearly positive
  let q:∃ u:ℝ, u = √(y/x) := by
    simp only [exists_eq]
  obtain ⟨u, udef⟩ := q
  let q:∃ v:ℝ, v = √(x*y) := by
    simp only [exists_eq]
  obtain ⟨v, vdef⟩ := q
  -- compute uv and v/u
  have h3:u*v = y := by
    rw [udef, vdef, ← Real.sqrt_mul (by apply div_nonneg; linarith; linarith), show y / x * (x * y) = (x/x)*y^2 by ring_nf, div_self (by positivity), one_mul, Real.sqrt_sq (by positivity)]
  have h4:v/u = x := by
    rw [udef, vdef, ← Real.sqrt_div (by positivity), ← div_mul, mul_div_assoc, div_self (by positivity), mul_one, show x*x=x^2 by ring, Real.sqrt_sq (by positivity)]
  -- we can now express the system in u and v
  rw [← vdef, ← udef, ← h3, show u * v - 2 * v - u + 2 = (u-2)*(v-1) by ring] at h1
  rw [← h3, ← h4, show 3 * (v / u) ^ 2 * (u * v) ^ 2 = 3 * (u/u)^2*v^4 by ring_nf, div_self (by rw [udef]; positivity), one_pow, mul_one] at h2;
  simp at h1
  -- simple now, just case analysis
  cases' h1 with h1 h1
  · have hu: u=2 := by linarith
    rw [hu] at h2; ring_nf at h2
    apply congr_arg (fun t => t/19) at h2; ring_nf at h2
    apply congr_arg (fun t => t^(1/4:ℝ)) at h2
    rw [show v^4=v^(4:ℝ) by norm_cast, ← Real.rpow_mul, mul_div, mul_one, div_self (by norm_num), Real.rpow_one] at h2
    rw [hu, h2] at h3 h4
    right
    constructor
    rw [← h4, show (2:ℝ) = (2^(4:ℝ))^(1/4:ℝ) by rw [← Real.rpow_mul];norm_num; simp, ← Real.div_rpow]; ring_nf; norm_num; norm_num
    rw [← h3]; ring_nf; rw [vdef]; positivity
  · have hv: v=1 := by linarith
    rw [hv] at h2; ring_nf at h2
    apply congr_arg (fun t => t-3) at h2; ring_nf at h2
    apply congr_arg (fun t => t^(1/4:ℝ)) at h2
    rw [show (81:ℝ)=3^(4:ℝ) by norm_num, show u^4=u^(4:ℝ) by norm_cast, ← Real.rpow_mul, ← Real.rpow_mul] at h2
    norm_num at h2
    left
    constructor
    rw [← h4, hv, h2]; ring_nf
    rw [← h3, hv, h2]; ring_nf
    norm_num
    rw [udef]; positivity