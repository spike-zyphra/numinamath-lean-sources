import Mathlib
open Complex

/-- A function $f$ is defined on the complex numbers by $f(z)=(a+bi)z$, where a​ and b​ are positive numbers.
  This function has the property that the image of each point in the complex plane is equidistant from that point
  and the origin.  Given that $∣a+bi∣=8$ and that $b^2=m/n$ where $m$​ and $n$​ are relatively prime positive integers, find $m+n$. -/
theorem algebra_97198 (f : ℂ → ℂ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  (hf : ∀ z, f z = (a + b * I) * z) (h : ∀ z, dist (f z) z = dist (f z) 0)
  (h' : abs (a + b * I) = 8) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
  (hmn : Nat.Coprime m n) (h'' : b ^ 2 = m / n) :
    m + n = 259 := by
  -- Suppose we pick an arbitrary point on the complex plane, say $(1,0)$.
  -- According to the definition of $f(z)$, $f(1) = (a+bi)1 = a + bi$.
  have f_val : f 1 = a + b * I := by
    rw[hf, mul_one]
  -- this image must be equidistant from $(1,0)$ and $(0,0)$
  have same_dist_classification (z : ℂ) (h : dist z 1 = dist z 0) : z.re = 1/2 := by
    rcases z with ⟨x,y⟩
    change x = 1/2
    rw[Complex.dist_eq, Complex.dist_eq, Complex.abs_eq_sqrt_sq_add_sq, Complex.abs_eq_sqrt_sq_add_sq] at h
    simp only [sub_re, one_re, sub_im, one_im, sub_zero] at h
    rw[Real.sqrt_eq_iff_eq_sq, Real.sq_sqrt] at h
    linarith
    · apply add_nonneg (sq_nonneg _) (sq_nonneg _)
    · apply add_nonneg (sq_nonneg _) (sq_nonneg _)
    · apply Real.sqrt_nonneg
  -- hence $a = 1/2$.
  have f_eq := same_dist_classification _ (h _)
  rw[hf] at f_eq
  norm_num at f_eq
  -- by the Pythagorean theorem, we have $(1/2)^2 + b^2 = 8^2$,
  rw[f_eq, Complex.abs_add_mul_I] at h'
  rw[Real.sqrt_eq_iff_eq_sq (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)] at h'
  -- hence $b^2 = 255/4$
  have b_sq_eq : b^2 = 255/4 := by
    rw[← eq_sub_iff_add_eq'] at h'
    rw[h']
    ring
  -- and once we show coprimality, we can see that
  have eq : m = 255 ∧ n = 4 := by
    have : m = (255 : ℤ) ∧ n = (4 : ℤ) := by
      apply Rat.div_int_inj
      · assumption_mod_cast
      · simp
      · assumption_mod_cast
      · decide
      rify
      exact h''.symm.trans b_sq_eq
    zify
    assumption
  -- the answer is 259.
  rw[eq.1, eq.2]