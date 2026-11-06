import Mathlib

/- 8. Let $a, b, c$ be positive real numbers, and satisfy $a b c=1$, prove that: $\frac{1}{a^{3}(b+c)}+\frac{1}{b^{3}(c+a)}+\frac{1}{c^{3}(a+b)} \geqslant$ $\frac{3}{2}$. -/
theorem inequalities_140535 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 / 2 ≤ 1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (c + a)) + 1 / (c ^ 3 * (a + b)) := by
  -- let x=1/a, y=1/b, z=1/c
  let q:∃ x:ℝ, x = 1/a := by
    simp only [exists_eq]
  obtain ⟨x, xdef⟩ := q
  let q:∃ y:ℝ, y = 1/b := by
    simp only [exists_eq]
  obtain ⟨y, ydef⟩ := q
  let q:∃ z:ℝ, z = 1/c := by
    simp only [exists_eq]
  obtain ⟨z, zdef⟩ := q
  -- clearly xyz = 1
  have hxyz : x * y * z = 1 := by rw [xdef, ydef, zdef]; ring_nf; field_simp; linarith
  -- transform the equation
  rw [show a = 1/x by aesop, show b = 1/y by aesop, show c = 1/z by aesop]; field_simp
  -- x, y, z are positive
  have hx: 0 < x := by aesop
  have hy: 0 < y := by aesop
  have hz: 0 < z := by aesop
  -- so we can simplify
  rw [show 1/y=x*z by exact Eq.symm (eq_one_div_of_mul_eq_one_left (by linarith)), show 1/z=x*y by exact Eq.symm (eq_one_div_of_mul_eq_one_left (by linarith)), show 1/x=y*z by exact Eq.symm (eq_one_div_of_mul_eq_one_left (by linarith)),
      ← mul_add, show x*y+y*z = y*(x+z) by ring_nf, ← add_mul, mul_comm (y+x),
      show x^3=x^2*x by ring_nf, ← mul_div, ← div_div, div_self (by positivity), mul_div, mul_one,
      show y^3=y^2*y by ring_nf, ← mul_div, ← div_div, div_self (by positivity), mul_div, mul_one,
      show z^3=z^2*z by ring_nf, ← mul_div, ← div_div, div_self (by positivity), mul_div, mul_one,
  ]
  -- this is a simple cauchy-schwarz
  have h1: (x+y+z)^2 ≤ ((y+z)+(z+x)+(x+y))*(x^2/(z+y) + y^2/(x+z) + z^2/(x+y)) := by
    let q:∃ v:EuclideanSpace ℝ (Fin 3), v = ![x/√(z+y), y/√(x+z), z/√(x+y)] := by
      simp only [exists_eq]
    obtain ⟨v, vdef⟩ := q
    let q:∃ w:EuclideanSpace ℝ (Fin 3), w = ![√(z+y), √(x+z), √(x+y)] := by
      simp only [exists_eq]
    obtain ⟨w, wdef⟩ := q
    have h' := real_inner_mul_inner_self_le v w; rw [show inner v w * inner v w = (inner v w)^2 by ring] at h';
    simp at h'; rw [vdef, wdef] at h';
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three] at h';
    simp at h';
    rw [show x / √(z + y) * √(z + y) + y / √(x + z) * √(x + z) + z / √(x + y) * √(x + y) = x * (√(z + y)/ √(z + y))  + y * (√(x + z)/ √(x + z))  + z * (√(x + y)/ √(x + y)) by ring_nf,
        div_self (by positivity), div_self (by positivity), div_self (by positivity), mul_one, mul_one, mul_one,
        show (x / √(z + y) * (x / √(z + y)) + y / √(x + z) * (y / √(x + z)) + z / √(x + y) * (z / √(x + y))) * (√(z + y) * √(z + y) + √(x + z) * √(x + z) + √(x + y) * √(x + y)) = (x^2 / √(z + y)^2 + y^2 / √(x + z)^2 + z^2 / √(x + y)^2) * (√(z + y)^2 + √(x + z)^2 + √(x + y)^2) by ring_nf,
        Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)
    ] at h';
    have h2:(x ^ 2 / (z + y) + y ^ 2 / (x + z) + z ^ 2 / (x + y)) * (z + y + (x + z) + (x + y)) = (y + z + (z + x) + (x + y)) * (x ^ 2 / (y + z) + y ^ 2 / (x + z) + z ^ 2 / (x + y)) := by ring_nf
    linarith
  rw [show (x+y+z)^2 = (x+y+z)*(x+y+z) by ring_nf, show (y + z + (z + x) + (x + y)) = (x+y+z)*2 by ring_nf, mul_assoc] at h1
  apply (mul_le_mul_iff_of_pos_left (by positivity)).mp at h1
  rw [show x+y+z = 2*((x+y+z)/2) by ring_nf, add_comm x] at h1
  apply (mul_le_mul_iff_of_pos_left (by positivity)).mp at h1
  suffices 3/2 ≤ (x+y+z)/2 by linarith
  refine div_le_div_of_nonneg_right ?_ (by norm_num);
  -- this can be shown by am-gm
  have q:= Real.geom_mean_le_arith_mean3_weighted (w₁:=1/3) (w₂:=1/3) (w₃:=1/3) (p₁:=x) (p₂:=y) (p₃:=z) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) (by norm_num)
  rw [← Real.mul_rpow (by positivity) (by positivity), ← Real.mul_rpow (by positivity) (by positivity), hxyz, Real.one_rpow] at q; linarith