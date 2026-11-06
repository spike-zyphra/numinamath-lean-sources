import Mathlib

open Complex

/- Let z=a+bi be the complex number with ∣z∣=5 and b>0 such that the distance between (1+2i)z^3 and z^5  is maximized, and let z^4=c+di. Find c+d. -/
theorem algebra_95362 {z : ℂ} (hz : abs z = 5) (hzz : z.im > 0) (h : ∀ w : ℂ, (abs w = 5) → (w.im > 0) → Complex.abs ((1 + 2 * I) * z ^ 3 - z ^ 5) ≥ Complex.abs ((1 + 2 * I) * w ^ 3 - w ^ 5)) : (z^4).re + (z^4).im = 125 := by
  -- first prove a lemma that |w| = 5 implies |(1+2i) * w^3 - w^5| = 125 * |w^2 + (-1-i)|
  have hsimp (w : ℂ) (hw: abs w = 5) : Complex.abs ((1 + 2 * I) * w ^ 3 - w ^ 5) = 125 * Complex.abs (w^2 + (- 1 - 2*I)) := by calc
    Complex.abs ((1 + 2 * I) * w ^ 3 - w ^ 5) = Complex.abs (w^3 * ((1 + 2 * I)  - w ^ 2)) := by congr; ring
    _ = Complex.abs (w^3) * Complex.abs ((1 + 2 * I)  - w ^ 2) := by simp
    _ = 125 * Complex.abs ((1 + 2 * I)  - w ^ 2) := by congr; simp [hw]; norm_num
    _ = 125 * Complex.abs (-((1 + 2 * I)  - w ^ 2)) := by simp [-neg_sub]
    _ = 125 * Complex.abs (w^2 + (- 1 - 2*I)) := by ring_nf
  -- |w| = 5 implies |w|^2 + |-1-2i| = 25 + √5
  have abs_sum_vals (w : ℂ) (hw : abs w = 5) : Complex.abs (w^2) + Complex.abs (-1-2*I) = 25 + √5 := by
    simp [hw]
    dsimp [Complex.abs, normSq]
    norm_num
  -- |(1+2i)*z^3 - z^5| ≤ 125 * (25 + √5) as sum of absolute values is greater or equal to absolute value of sums
  have : Complex.abs ((1 + 2 * I) * z ^ 3 - z ^ 5) ≤ 125 * (25 + √5) := by calc
    Complex.abs ((1 + 2 * I) * z ^ 3 - z ^ 5) = 125 * Complex.abs (z^2 + (- 1 - 2*I)) := by simp [hsimp, hz]
    _ ≤ 125 * (Complex.abs (z^2) + Complex.abs (-1-2*I)) := by
      gcongr
      exact AbsoluteValue.add_le Complex.abs _ _
    _ = 125 * (25 + √5) := by rw [abs_sum_vals _ hz]
  -- 125 * (25 + √5) ≤ |(1+2i)*z^3 - z^5|, to prove this, we'll find a suitable w to plug into h
  have : 125 * (25 + √5) ≤ Complex.abs ((1 + 2 * I) * z ^ 3 - z ^ 5) := by
    -- first of all, there exists w=  √(√5 * (-5-10i)) which has positive imaginary part
    have h_exists : ∃ w:ℂ, w^2 = √5 * (-5 - 10*I) ∧ w.im > 0 := by
      set w := (√5 * (-5 - 10*I))^((1:ℂ)/2) with hw
      have hw_sq : w^2 = √5 * (-5 - 10*I) := by rw [hw]; simp
      obtain h | h | h := lt_trichotomy (w.im) 0
      . use (-w)
        constructor <;> (simp; assumption)
      . have : (w^2).im = 0 := by rw [sq, mul_im, h]; simp
        rw [hw_sq] at this
        simp at this
      . use w
    -- next such w has absolute value of 5
    obtain ⟨w, hw₁, hw₂⟩ := h_exists
    have hw₃ : Complex.abs w = 5 := by calc
      Complex.abs w = √((Complex.abs w)^2) := by simp
      _ = √(Complex.abs (w^2)) := by simp
      _ = √(Complex.abs (√5 * (-5 - 10 * I))) := by rw [hw₁]
      _ = √(5^2) := by
        congr
        dsimp [Complex.abs, Complex.normSq]
        ring_nf
        simp
        rw [← Real.sqrt_mul]
        norm_num
        rw [(by norm_cast: (625:ℝ) = 25^2)]
        simp
        norm_num
      _ = 5 := by simp
    -- plug in w into h and then do some manipulation to get the inequality
    have ht := h w hw₃ hw₂
    nth_rw 2 [hsimp] at ht
    any_goals assumption
    rw [hw₁] at ht
    have :  Complex.abs (↑√5 * (-5 - 10 * I) + (-1 - 2 * I)) = 25 + √5 := by
      dsimp [Complex.abs, Complex.normSq]
      repeat (simp; ring_nf)
      calc
        √(630 + √5 * 50) = √(25^2 + 2 * 25 * √5 + (√5)^2) := by simp; ring_nf
        _ = √((25 + √5)^2) := by ring_nf
        _ = 25 + √5 := by
          rw [Real.sqrt_sq]
          positivity
    rw [this] at ht
    assumption
  -- the two inequality imply |(1+2i)*z^3 - z^5| = 125 * (25 + √5), but lhs is 125 * |z^2 + (-1-2i)| and rhs is 125 *|z^2| + |-1-2i|, this means -1-2i and z^2 have same argument
  have h' : Complex.abs ((1 + 2 * I) * z ^ 3 - z ^ 5) = 125 * (25 + √5) := by linarith
  rw [hsimp _ hz] at h'
  simp at h'
  rw [← abs_sum_vals _ hz] at h'
  obtain h | h | h_arg := Complex.abs_add_eq_iff.mp h'
  . have: z = 0 := by exact pow_eq_zero h
    rw [this] at hzz
    simp at hzz
  . have := congrArg Complex.re h
    simp at this
    -- with same argument, we can construct z^2 as |z^2| * exp(arg(-1-2i) * i) = √5 * (-5-10i)
  . have := Complex.abs_mul_exp_arg_mul_I (-1-2*I)
    dsimp [Complex.abs, normSq] at this
    norm_num at this
    have hz_sq : z^2 = √5 * (-5 - 10*I) := by calc
      z^2 = (abs (z^2)) * exp (arg (z^2) * I) := by rw [Complex.abs_mul_exp_arg_mul_I]
      _ = 25 * exp (arg (-1-2*I) * I) := by rw [h_arg]; congr; simp [hz]; norm_num
      _ = 5 * √5 * (√5  * exp (arg (-1-2*I) * I)) := by
        ring_nf; norm_cast; simp; ring
      _ = 5 * √5 * (-1 - 2*I) := by rw [this]
      _ = √5 * (-5 - 10*I) := by ring
    -- finally plug into z^4 to get value -375 + 500i, so answer is -375+500=125
    have : z^4 = -375 + 500*I := by calc
      z^4 = (z^2)^2 := by ring
      _ = (√5 * (-5 - 10*I))^2 := by rw [hz_sq]
      _ = -375 + 500*I := by
        ring_nf
        norm_cast
        simp
        ring
    rw [this]
    simp
    norm_num