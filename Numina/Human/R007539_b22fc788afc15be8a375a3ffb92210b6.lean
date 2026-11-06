import Mathlib

/- The polynomial $f(z) = az^{2018} + bz^{2017} + cz^{2016}$ has real coefficients not exceeding $2019$,
and $f\left(\frac{1 + \sqrt{3}i}{2}\right) = 2015 + 2019\sqrt{3}i$. Find the remainder when $f(1)$ is divided by $1000$. -/
theorem algebra_98027 {a b c : ℝ} (ha : a ≤ 2019) (hb : b ≤ 2019) (hc : c ≤ 2019)
    (f : ℂ → ℂ) (hf : ∀ z, f z = a * z ^ 2018 + b * z ^ 2017 + c * z ^ 2016)
    (h : f ((1 + √3 * Complex.I) / 2) = 2015 + 2019 * √3 * Complex.I) (n : ℤ) (hn : n = f 1) :
    n % 1000 = 53 := by

  -- First we show that ω = (1 + √3 i) / 2 is equal to exp(πi/3).
  let ω := (1 + √3 * Complex.I) / 2

  let circle : ℝ → ℂ := fun θ => Complex.exp (θ * Complex.I)

  have hω_circle : ω = circle (Real.pi / 3) := by
    simp only [circle, ω, Complex.ext_iff]
    and_intros
    . rw [Complex.exp_ofReal_mul_I_re]
      simp
    . rw [Complex.exp_ofReal_mul_I_im]
      simp

  -- This is a (primitive) sixth root of unity.
  have hω6 : ω ^ 6 = 1 := by
    simp [hω_circle, circle]
    rw [← Complex.exp_nat_mul]
    rw [← Complex.exp_two_pi_mul_I]
    ring_nf

  -- From this we can compute ω^2 too.
  have hω2_circle : ω ^ 2 = circle (Real.pi - Real.pi / 3) := by
    rw [hω_circle]
    rw [← Complex.exp_nat_mul]
    simp [circle]
    ring_nf

  have hω2 : ω ^ 2 = (-1 + √3 * Complex.I) / 2 := by
    simp only [hω2_circle, circle, Complex.ext_iff]
    and_intros
    . rw [Complex.exp_ofReal_mul_I_re]
      simp
      norm_num
    . rw [Complex.exp_ofReal_mul_I_im]
      simp

  -- We can now use the fact that f(ω) = 2015 + 2019√3i.
  have r1 : f ω = a * ω ^ 2 + b * ω + c := calc
    f ω = a * ω ^ 2018 + b * ω ^ 2017 + c * ω ^ 2016 := by rw [hf]
    _ = (a * ω ^ 2 + b * ω + c) * (ω ^ (6 : ℂ)) ^ (336 : ℕ) := by
      rw [← Complex.cpow_mul_nat ω 6 336]
      norm_num
      rw [add_mul, add_mul, mul_assoc, mul_assoc, ← pow_succ', ← pow_add]
    _ = (a * ω ^ 2 + b * ω + c) * (ω ^ 6) ^ (336 : ℕ) := by simp
    _ = a * ω ^ 2 + b * ω + c := by rw [hω6]; simp

  -- We can equate the real and imaginary part to find equations for a, b, and c.
  have r2 : (- 1 / 2) * a + (1 / 2) * b + c = 2015 := calc
    (- 1 / 2) * a + (1 / 2) * b + c = (f ω).re := by rw [r1, hω2]; simp [ω]; ring_nf
    _ = (2015 + 2019 * √3 * Complex.I).re := by simp only [ω]; rw [h]
    _ = 2015 := by simp

  apply_fun (fun x => 2 * x) at r2
  ring_nf at r2

  have r3 : (√3 / 2) * a + (√3 / 2) * b = 2019 * √3 := calc
    (√3 / 2) * a + (√3 / 2) * b = (f ω).im := by rw [r1, hω2]; simp [ω]; ring_nf
    _ = (2015 + 2019 * √3 * Complex.I).im := by simp only [ω]; rw [h]
    _ = 2019 * √3 := by simp

  apply_fun (fun x => (2 / √3) * x) at r3
  ring_nf at r3
  simp at r3

  -- We can now solve the equations using the bounds on a, b, and c, and compute f(1).
  have ha : a = 2019 := by linarith
  have hb : b = 2019 := by linarith
  have hc : c = 2015 := by linarith

  have : f 1 = 6053 := by
    rw [hf, ha, hb, hc]
    norm_num

  rw [this] at hn
  norm_cast at hn
  rw [hn]
  simp