import Mathlib

/-Find the positive value of t that satisfies ab = t-2i given |a| = 2 and |b| = √26 -/
theorem algebra_15416 {a b : ℂ} {t : ℝ} (ht : 0 < t) (ha : Complex.abs a = 2) (hb : Complex.abs b = Real.sqrt 26)
    (h : a * b = t - (2 : ℝ) * .I) :
    t = 10 := by
  -- prove ‖a‖‖b‖ = ‖a * b‖
  have eq1 : Complex.abs a * Complex.abs b = Complex.abs (a * b) := by
    norm_num
  -- substitute a, b, a * b in the hypothesis
  rw [ha, hb, h] at eq1
  have eq2 : 2 * √26 = Complex.abs (t + ((-2) : ℝ) * Complex.I) := by rw[eq1]; norm_num; ring_nf
  -- use ‖t - 2i‖ = √(t ^ 2 + 4) ,so that we have √(t ^ 2 + 4) = 2√26
  have eq3 : √(t ^ 2 + 4) = 2 * √26 := by
    rw [Complex.abs_add_mul_I] at eq2
    symm at eq2
    norm_num at eq2
    exact eq2
  -- simpilfy eq3 to t ^ 2 + 4 = 104
  have eq4 : t ^ 2 + 4 = 104 := by
    rw [@Real.sqrt_eq_iff_eq_sq] at eq3
    ring_nf at eq3
    rw [Real.sq_sqrt] at eq3
    nlinarith only [eq3, ht]
    repeat positivity
  
  -- finally get the answer
  nlinarith only [eq4, ht]
  