import Mathlib

/- A sequence $(a_1,b_1)$, $(a_2,b_2)$, $(a_3,b_3)$, $\ldots$ of points in the coordinate plane satisfies
\[(a_{n + 1}, b_{n + 1}) = (\sqrt {3}a_n - b_n, \sqrt {3}b_n + a_n)\]for $n = 1,2,3,\ldots$.  Suppose that $(a_{100},b_{100}) = (2,4)$. What is $a_1 + b_1$?  Express your answer using exponential notation. -/
theorem calculus_16542 {a b : ℕ → ℝ} (ha : ∀ n, a (n + 1) = Real.sqrt 3 * a n - b n)
    (hb : ∀ n, b (n + 1) = Real.sqrt 3 * b n + a n) (ha0 : a 100 = 2) (hb0 : b 100 = 4) :
    a 1 + b 1 = 1 / 2 ^ 98 := by
  -- let z = a+bi
  let z : ℕ → ℂ := fun n => (a n + Complex.I * b n)
  have z_def: z = fun n => (a n + Complex.I * b n) := rfl
  have z_def'(n:ℕ): z n = a n + Complex.I * b n := by
    rw [z_def]
  -- notice that z (n+1) = (√3+i)zn
  have hz(n:ℕ)(hn:n ≥ 1): z (n+1) = (√3+Complex.I) * z n := by
    rw [z_def' (n+1), ha n, hb n]
    have h1: ↑(√3 * a n - b n) = √3 * a n + (Complex.I*Complex.I)*b n
      := by simp; ring
    rw [h1, z_def' n]; ring_nf; simp; ring
  -- so z100 = (√3+i)^99 z1
  have hz1(n:ℕ)(hn:n ≥ 1): z (n+1) = (√3+Complex.I)^n * z 1 := by
    induction' n with d hd
    · simp
    · rw [hz (d+1) hn]
      by_cases hhd: d = 0
      · rw [hhd]; simp
      · have dge1: d ≥ 1 := by
          push_neg at hhd
          exact Nat.one_le_iff_ne_zero.mpr hhd
        rw [hd dge1]; ring
  have hz2: z 100 = (√3+Complex.I)^99 * z 1 := by
    have: 100 = 99+1 := by simp
    rw [this, hz1 99 (by norm_num)]
  -- notice that √3+i = 2x(√3/2+1/2xi)=2cis(π/6), or, e^(iπ/6)
  have hcis: √3+Complex.I = 2*Complex.exp (Real.pi/6 * Complex.I) := by
    rw [Complex.exp_mul_I]
    have: ↑Real.pi/(6:ℂ) = ↑(Real.pi/6) := by simp
    rw [this, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [Real.cos_pi_div_six, Real.sin_pi_div_six]; simp; ring
  -- so (√3+i)^99 = 2^99 * (e^(π/6))^99
  have h1: (√3+Complex.I)^99 = 2^99 * Complex.I := by
    rw [hcis, mul_pow]
    have ht1: Complex.exp (Real.pi/6 * Complex.I)^99 =
      Complex.exp (↑(99:ℕ)*(Real.pi/6 * Complex.I)) := by
      rw [Complex.exp_nat_mul]
    -- notice that 96 = 6x16 = 12x8, so 99 π/6 = 3π/6 + 2kπ = π/2+2kπ
    have ht2: ↑(99:ℕ)*(Real.pi/6 * Complex.I) =
      ↑(Real.pi/2) * Complex.I + ↑(8:ℕ) * (2*Real.pi*Complex.I)
      := by simp; ring
    have ht3: Complex.exp (↑(99:ℕ)*(Real.pi/6 * Complex.I)) =
      Complex.I := by
      rw [ht2, Complex.exp_add]
      rw [Complex.exp_nat_mul_two_pi_mul_I]
      rw [Complex.exp_mul_I]
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
      rw [Real.cos_pi_div_two, Real.sin_pi_div_two]; simp
    rw [ht1, ht3]
  have h2: z 100 = 2 + 4*Complex.I := by
    rw [z_def' 100, ha0, hb0]; simp; ring
  -- substitute to hz2 and solve z1
  have h3: z 1 = (2+4*Complex.I) / (2^99*Complex.I) := by
    rw [hz2, h1] at h2
    rw [← h2]; simp
  -- simplify, mul I on both sides of the fraction.
  have h4: (2+4*Complex.I) / (2^99*Complex.I) =
    2/(2^98) - 1/(2^98) * Complex.I := by
    field_simp
    have ht1: (2 - Complex.I) * (2 ^ 99 * Complex.I) =
      4*2^98*Complex.I + 2^99 := by
      rw [sub_mul]; ring_nf; simp; ring
    rw [ht1]; ring
  -- thus we can solve a1 and b1, they are real and imaginary part of z1.
  have ha1: a 1 = 2/(2^98) := by
    have ht1: (z 1).re = a 1 := by
      rw [z_def']; simp
    have ht2: (z 1).re = 2/(2^98) := by
      have: ((2:ℂ)^98).im = 0 := by
        norm_num
      rw [h3, h4]; simp [this]
      have: (2:ℂ)/2^98 = ↑((2:ℝ) / (2^(98:ℕ))) := by simp
      rw [this]
      apply rfl
    rwa [ht1] at ht2
  have ha2: b 1 = - 1/(2^98) := by
    have ht1: (z 1).im = b 1 := by
      rw [z_def']; simp
    have ht2: (z 1).im = -1/(2^98) := by
      rw [h3, h4]
      have hh1: ((2:ℂ) / 2 ^ 98).im = 0 := by norm_num
      have hh2: (2 / 2 ^ 98 - 1 / 2 ^ 98 * Complex.I).im =
        (2 / 2 ^ 98 :ℂ).im - (1/2^98 * Complex.I).im := rfl
      have hh3: (1 / 2 ^ 98 :ℂ) = (↑(1/2^98 :ℝ):ℂ) := by simp
      have hh4: (↑(1/2^98 :ℝ) * Complex.I).im = 1/2^98 := by
        rw [Complex.mul_I_im]; rfl
      rw [hh2, hh1, hh3, hh4]
      ring
    rwa [ht1] at ht2
  -- substitute, thus a1+b1 is determined.
  rw [ha1, ha2]; ring