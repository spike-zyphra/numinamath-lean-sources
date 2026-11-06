import Mathlib



/- 4. Let $x, y, z$ be positive numbers, and $x^{2}+y^{2}+z^{2}=1$. Try to find the minimum value of the following expression:

$$

S=\frac{x y}{z}+\frac{y z}{x}+\frac{z x}{y} .

$$

(22nd All-Soviet Union Olympiad) -/
theorem inequalities_290816 :
  IsLeast {s : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^2 + y^2 + z^2 = 1 ∧ s = (x * y) / z + (y * z) / x + (z * x) / y} (Real.sqrt 3) := by
  constructor
    -- first prove √3 belongs to set by using x = y = z = 1/√3
  . use 1 / √3, 1 / √3, 1 / √3
    simp
    ring_nf
    field_simp
    -- next prove √3 is a lower bound
  . rintro s ⟨x, y, z, hx, hy, hz, hxyz, hs⟩
    -- prove a version of am-gm ineq for 2 variables as that will be used
    have amgm (p q : ℝ) (hp : 0 < p) (hq: 0 < q) : 4*p*q ≤ (p + q)^2 := by
      ring_nf
      have : 0 ≤ p^2 - p*q*2 + q^2 := by calc
        0 ≤ (p-q)^2 := by positivity
        _ = _ := by ring
      linarith

    -- using amgm prove that 4*q^2 ≤  p^2 * q^2 / r^2 + 2 * q^2 +  q^2 * r^2 / p^2 for positive p, q, r
    have amgm' {p q r : ℝ} (hp: p > 0) (hq: q > 0) (hr: r > 0) : 4*q^2 ≤  p^2 * q^2 / r^2 + 2 * q^2 +  q^2 * r^2 / p^2 := by
      have := amgm (p*q/r) (q*r/p) (by positivity) (by positivity)
      convert this using 1
      repeat field_simp; ring_nf

    -- apply last lemma on x, y, z; y, z, x; z, x, y
    have := amgm' hx hy hz
    have := amgm' hy hz hx
    have := amgm' hz hx hy

    -- merging last 3 inequalities provides following inequality, where rhs is actually s^2
    have h_ineq : 3 * (x^2 + y^2 + z^2) ≤ x^2 * y^2 / z^2 + y^2 * z^2 / x^2 + z^2 * x^2 / y^2 + 2 * (x^2 + y^2 + z^2) := by
      linarith
    nth_rw 1 [hxyz] at h_ineq

    have hs' : s^2 = x^2 * y^2 / z^2 + y^2 * z^2 / x^2 + z^2 * x^2 / y^2 + 2 * (x^2 + y^2 + z^2) := by
      rw [hs]
      field_simp
      ring

    rw [← hs'] at h_ineq
    -- so 3 ≤ s^2, target is easy to prove now.
    norm_num at h_ineq
    have : 0 ≤ s := by rw [hs]; positivity
    rw [← Real.sqrt_sq ‹0 ≤ s›]
    exact Real.sqrt_le_sqrt h_ineq