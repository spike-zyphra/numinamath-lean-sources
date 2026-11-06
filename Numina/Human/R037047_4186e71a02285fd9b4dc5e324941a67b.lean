import Mathlib

open Real 
open Complex 

/- Given $f(z) = z^2-19z$, there are complex numbers $z$ with the property that $z$, $f(z)$, and $f(f(z))$ are the vertices of a right triangle in the complex plane with a right angle at $f(z)$.
There are positive integers $m$ and $n$ such that one such value of $z$ is $m+\sqrt{n}+11i$. Find $m+n$. -/
theorem algebra_97738 (f : ℂ → ℂ) (hf : ∀ w, f w = w ^ 2 - 19 * w)
    (z : ℂ) (hz : z ≠ 0) (h : ((f (f z) - f z) * (starRingEnd ℂ) (f z - z)).re = 0)
    (m n : ℕ) (hnpos : n > 0) (hmpos : m > 0) (hn_ne_sq : ∀ k, (n : ℝ) ≠ k ^ 2) (h' : m > 0 ∧ n > 0 ∧ z = m + sqrt n + 11 * .I) :
    m + n = 230 := by
    obtain ⟨hm, hn, hmn⟩ := h'
    --the real part of z is m + sqrt n and the imaginary part is 11
    have hz_re_im : z.re = m + sqrt n ∧ z.im = 11 := by
        rw[hmn]
        constructor
        · rw[add_re]
          simp
        · rw[add_im]
          simp
    -- z is not 20 and the conjugate of z is not 20
    have hz20 : z ≠ 20 ∧ (starRingEnd ℂ) z ≠ 20:= by
        constructor
        · by_contra l
          rw[l] at hz_re_im
          obtain ⟨hzrm1,hzrm2⟩:=hz_re_im
          rw[(by exact rfl : im 20 = 0)] at hzrm2
          linarith
        · by_contra l
          have im_op : - z.im = -11 := by linarith
          rw[← conj_im, l] at im_op
          rw[(by exact rfl : im 20 = 0)] at im_op
          linarith
    -- f(f(z)) - f(z) / f(z) - z is purely imaginary, that reflects the fact that the triangle is right-angled at f(z)
    have him : ((f (f z) - f z) / (f z - z)).re = 0 := by
      have eq_fz : (f (f z) - f z) / (f z - z) = (f (f z) - f z) * (starRingEnd ℂ) (f z - z) / ((f z - z) * (starRingEnd ℂ) (f z - z)) := by 
        rw[mul_div_mul_comm, div_self]
        ring_nf
        specialize hf z
        rw[hf, (by ring_nf : z ^ 2 - 19 * z - z = z * (z - 20))]
        simp
        constructor
        · exact hz
        · rw[(by exact conj_eq_iff_re.mpr rfl : (starRingEnd ℂ) 20 = 20)]
          exact sub_ne_zero.2 hz20.2
      rw[eq_fz, mul_conj (f z - z)]
      simp at h
      simp
      left
      rw[h]
    -- f(t) - t = t * (t - 20) is a polynomial identity
    have hff : ∀ t : ℂ, f t - t = t * (t - 20) := by
      intro t
      specialize hf t
      rw[hf]
      ring_nf
    -- f(f(z)) - f(z) = f(z) * (f(z) - 20) using the above identity
    have hff' : (f (f z) - f z) / (f z - z) = (z - 9) ^ 2 - 100 := by
      have hff_num : f (f z) - f z = f z * (f z - 20) := by specialize hff (f z); exact hff
      specialize hff z
      specialize hf z
      rw[hff_num, hff, hf]
      nth_rewrite 1 [(by rw[mul_sub]; ring_nf : (z ^ 2 - 19 * z) = z * (z - 19))]
      rw[(by rw[sub_mul]; ring_nf : (z ^ 2 - 19 * z - 20) = (z - 20) * (z + 1))]
      have j : z * (z - 19) * ((z - 20) * (z + 1)) = ((z - 19) * (z + 1)) * (z * (z - 20)) := by ring_nf
      rw[j, ← mul_div_assoc', div_self (by exact mul_ne_zero hz (by exact sub_ne_zero.2 hz20.1))]
      ring_nf
    -- developing again we get re((z-9)^2) = 221
    have hh : (z - 9).re ^ 2 = 221 := by
      have hre : ((z - 9) ^ 2).re = 100 := by
        simp[hff'] at him
        linarith
      simp
      rw[sub_sq (z.re) 9]
      rw[sub_sq] at hre
      simp at hre
      nth_rewrite 1 [← re_add_im z] at hre
      rw[add_sq, add_re] at hre
      simp at hre
      rw[mul_pow, hz_re_im.2] at hre
      norm_cast at hre
      norm_num at hre
      linarith
    simp at hh
    -- this implies that the real part of z is either 9 + sqrt(221) or 9 - sqrt(221)
    have sqrt_root : z.re - 9 = sqrt 221 ∨ z.re - 9 = -sqrt 221 := by 
      rw[sub_sq, (by constructor; intro h; linarith; intro h; linarith : z.re ^ 2 - 2 * z.re * 9 + 9 ^ 2 = 221 ↔ z.re ^ 2 - 2 * z.re * 9 + 9 ^ 2 - 221 = 0)] at hh
      ring_nf at hh
      rw[(by linarith : -140 - z.re * 18 + z.re ^ 2 = 1 * (z.re * z.re) + (- 18) * z.re + (- 140))] at hh
      have disc : discrim 1 (-18) (-140) = sqrt (4 * 221) * sqrt (4 * 221) := by 
        rw[← pow_two, sq_sqrt]
        simp[discrim]
        ring_nf
        linarith
      rw[quadratic_eq_zero_iff (by linarith) disc z.re] at hh
      rw[sqrt_mul', add_div, sub_div] at hh
      rw[mul_comm (sqrt 4) (sqrt 221), ← mul_div_assoc'] at hh
      rw[(by norm_num : sqrt 4 = sqrt (2 * 2)), sqrt_mul'] at hh
      ring_nf at hh
      rw[sq_sqrt, mul_assoc, mul_assoc] at hh
      rw[(by norm_num : (2:ℝ) * ((-1:ℝ) / 2) = - (2 * (1 / 2)))] at hh
      rw[mul_one_div, div_self] at hh
      ring_nf at hh
      obtain hh1|hh2 := hh
      · left
        linarith
      · right
        linarith
      linarith
      linarith
      linarith
      linarith
    obtain hzre1|hzre2 := sqrt_root
    --the case where re(z) = 9 + sqrt 221 takes us to the conclusion
    · rw[hz_re_im.1] at hzre1
      have hm' : m = 9 := by 
        rw[(by linarith : (m : ℝ) + sqrt (n : ℝ) - 9 = ((m : ℝ) - 9) + sqrt (n : ℝ)), ← sq_eq_sq] at hzre1
        rw[add_sq, sub_sq] at hzre1
        simp at hzre1
        by_contra l
        have eq : sqrt (n : ℝ) = (221 - (n : ℝ) - (m : ℝ) ^ 2 + 2 * (m : ℝ) * 9 - 9 ^ 2) / (2 * ((m : ℝ) - 9)) := by
          rw[(by linarith : (221 - (n : ℝ) - (m : ℝ) ^ 2 + 2 * (m : ℝ) * 9 - 9 ^ 2) = (2 * ((m : ℝ) - 9)) * sqrt (n : ℝ))]
          nth_rewrite 1 [← mul_comm, mul_div_assoc, div_self (by exact mul_ne_zero (by norm_cast) (by exact sub_ne_zero.2 (by norm_cast)))]
          linarith
        by_cases he_neg : (221 - (n : ℝ) - (m : ℝ) ^ 2 + 2 * (m : ℝ) * 9 - 9 ^ 2) / (2 * ((m : ℝ) - 9)) ≤ 0
        · have hsqn_pos : sqrt n > 0 := by exact sqrt_pos_of_pos (by norm_cast)
          have contr : 1 < 0 := by linarith
          contradiction
        · have heq_pos : 0 < (221 - (n : ℝ) - (m : ℝ) ^ 2 + 2 * (m : ℝ) * 9 - 9 ^ 2) / (2 * ((m : ℝ) - 9)) := by linarith
          rw[← sq_eq_sq] at eq
          simp at eq
          rw[eq] at hn_ne_sq
          specialize hn_ne_sq ((221 - (n : ℝ) - (m : ℝ) ^ 2 + 2 * (m : ℝ) * 9 - 9 ^ 2) / (2 * ((m : ℝ) - 9)))
          contradiction
          apply le_of_lt (sqrt_pos.2 (by norm_cast))
          exact le_of_lt heq_pos
        rw[hzre1]
        norm_num
        norm_num
      rw[hm'] at hzre1
      push_cast at hzre1
      norm_num at hzre1
      norm_cast at hzre1
      rw[hm', hzre1] 
    -- the case where re(z) = 9 - sqrt 221 leads to a contradiction
    · rw[hz_re_im.1] at hzre2
      rw[(by constructor; intro l; linarith; intro l ; linarith : (m : ℝ) + sqrt (n:ℝ) - 9 = -√221 ↔ (m : ℝ) + sqrt (n:ℝ) = 9 - √221)] at hzre2
      have hsqn_pos : (m : ℝ) + sqrt n > 0 := by
        have hm_pos : (m : ℝ) > 0 := by norm_cast
        have hsq_pos : sqrt n > 0 := by exact sqrt_pos_of_pos (by norm_cast)
        linarith
      have hsq221_pos : 9 - sqrt 221 < 0 := by 
        norm_num
        have obv : 9 ^ 2 < (sqrt 221) ^ 2 := by norm_num
        rw[sq_lt_sq] at obv
        simp[abs_of_pos] at obv
        exact obv
      have contr : 1 < 0 := by linarith
      contradiction