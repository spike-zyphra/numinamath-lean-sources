import Mathlib

/- Determine all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that
$$
f\left(x^{3}+y^{3}+x y\right)=x^{2} f(x)+y^{2} f(y)+f(x y)
$$
for all $x, y \in \mathbb{R}$.-/
theorem algebra_604278{f: ℝ → ℝ}:
  (∀(x y:ℝ), f (x^3+y^3+x*y) = x^2 * f x + y^2 * f y + f (x*y)) ↔
  ∀x:ℝ, f x = x * f 1 := by
  apply Iff.intro ?_
  -- when f(x) = x(f1), it's easy to verify these condition are satisfied.
  · intro hf x y
    simp only [hf (x^3+y^3+x*y), hf x, hf y, hf (x*y)]
    ring
  -- now, we work on the other direction.
  intro hf
  -- take x=1 and y=0, we get f(0) = 0
  have hf0: f 0 = 0 := by
    have := hf 1 0
    simp only [one_pow, pow_three, pow_two, mul_one,
    mul_zero, zero_mul, one_mul, add_zero, self_eq_add_right] at this
    exact this
  -- take take x=x and y=0, f(x^3) = x^2f(x)
  have hfpx(x:ℝ): f (x^3) = x^2 * f x := by
    have h1 := hf x 0
    have h2: x^3 + 0^3 + x*0 = x^3 := by simp
    rw [← h2, h1]
    simp [hf0]
  -- fill first position with x, and let y=-x, f(x) = - f(-x)
  have hfnx(x:ℝ): f x = - f (-x) := by
    have h1: x^2 * f x + x^2 * f (-x) = 0 := by
      have := hf x (-x)
      have h1: x^3 + (-x)^3 + x * -x = x * -x := by ring
      have h2: (-x)^2 = x^2 := by simp only [even_two, Even.neg_pow]
      rw [h1, h2] at this
      simp only [mul_neg, self_eq_add_left] at this
      exact this
    have h2: x^2*(f x + f (-x)) = 0 := by
      rw [← h1]; ring
    rcases (mul_eq_zero.mp h2) with hh1 | hh2
    · replace hh1: x = 0 := pow_eq_zero hh1
      simp only [hh1, hf0, neg_zero]
    · linarith [h2]
  -- consider (x,y) - (x, -y)
  have h1(x y: ℝ): f (x^3+y^3+x*y) = 2 * f (x^3) + f (y^3+x*y-x^3) := by
    -- (x,y)
    have h1 := hf x y
    -- (x,-y)
    have h2 := hf x (-y)
    -- (x,y) - (x,-y)
    have h3: f (y^3) + f (x*y) = (f (x^3+y^3+x*y) - f (x^3+(-y)^3+x*-y))/2 := by
      rw [h1, h2]
      have: f (x * -y) = - f (x*y) := by
        have := hfnx (-(x*y))
        simp only [mul_neg, this, neg_neg]
      simp only [hfnx y, hfpx y, this]
      ring
    -- substitute back into h1
    rw [← hfpx y, add_assoc (x^2*f x) _ _, h3] at h1
    -- simplify
    have: f (x^3 + (-y)^3 + x * -y) = - f (y^3+x*y-x^3) := by
      rw [hfnx (x^3+(-y)^3+ (x*-y))]; congr
      ring
    rw [this, ← hfpx x] at h1
    linarith [h1]
  have h2(a b: ℝ): f (a+b) = 2 * f a + f (b-a) := by
    -- view a as x^3, and we want x^3+y^3+xy = a+b
    obtain ⟨x, hx⟩: ∃x:ℝ, x^3 = a := by
      by_cases ha: 0 ≤ a
      · use a^(1/3:ℝ)
        simp [← Real.rpow_mul_natCast ha]
      · have: 0 ≤ -a := by
          push_neg at ha
          apply le_of_lt
          simp [ha]
        use - (-a)^(1/3:ℝ)
        rw [neg_pow, ← Real.rpow_mul_natCast this]
        simp only [one_div, Nat.cast_ofNat, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true,
        inv_mul_cancel₀, Real.rpow_one, mul_neg]
        ring
    -- obviously, y^3+xy-b = 0 has at least one root.
    obtain ⟨y,hy⟩ : ∃y:ℝ, y^3 + x*y - b = 0 := by
      set f: ℝ → ℝ := fun y => y^3+x*y-b with f_def
      set g: ℝ → ℝ := fun y => 0 with g_def
      obtain ⟨y, hy⟩ : ∃ y, f y = g y := by
        -- show y^3+xy-b can ≤ 0
        obtain ⟨y1, hy1⟩ : ∃y, f y ≤ g y := by
          simp only [f_def, g_def, tsub_le_iff_right, zero_add]
          use (-|b|-|x|-1)
          replace h1: (-|b|-|x|-1)^3 + x*(-|b|-|x|-1) =
            (-|b|-|x|-1) * ((-|b|-|x|-1)^2 + x) := by ring
          have h2{aa bb: ℝ}(hbb: bb < 0)(haa: aa ≥ 1):
            bb ≥ bb*aa := by nlinarith [hbb, haa]
          have h3: (-|b|-|x|-1)^2+x ≥ 1 := by
            have hh1: (-|b|-|x|-1)^2 = (|b|+|x|+1)^2 := by
              rw [sq_eq_sq_iff_eq_or_eq_neg]
              right; ring
            have hh2: (|b|+|x|+1)^2 ≥ (|b|+|x|+1) := by
              apply le_self_pow₀ ?_ (by norm_num)
              linarith [abs_nonneg b, abs_nonneg x]
            have hh3: |b|+|x|+1 +x ≥ 1 := by
              linarith [neg_abs_le x, abs_nonneg b]
            rw [hh1]
            apply hh3.trans (by linarith [hh2])
          rw [h1]; calc
          _ ≤ -|b|-|x|-1 := by
            apply h2 ?_ h3
            linarith [abs_nonneg b, abs_nonneg x]
          _ ≤ -|b| := by linarith [abs_nonneg x]
          _ ≤ _ := neg_abs_le b
        -- show y^3+xy-b can ≥ 0
        obtain ⟨y2, hy2⟩: ∃y, g y ≤ f y := by
          simp only [g_def, f_def, sub_nonneg]
          by_cases hx: 0 < x
          · use (|b|/x); calc
            b ≤ |b| := le_abs_self b
            _ = x*(|b|/x) := by field_simp [hx]
            _ ≤ _ := by
              have: 0 ≤ (|b|/x)^3 := by
                apply pow_nonneg (div_nonneg (by simp) ?_)
                apply le_of_lt hx
              linarith [this]
          · push_neg at hx
            use (-x+|b|+1); calc
            b ≤ |b| := le_abs_self b
            _ ≤ -x + |b|+1 := by linarith [hx]
            _ ≤ (-x+|b|+1)*( (-x+|b|+1)^2+x) := by
              apply le_mul_of_one_le_right ?_ ?_
              · linarith [hx, abs_nonneg b]
              · apply (OrderedSub.tsub_le_iff_right _ _ _).mp
                calc
                  1-x ≤ -x+|b|+1 := by linarith [abs_nonneg b]
                  _ ≤ _ := by
                    apply le_self_pow₀ ?_ (by norm_num)
                    linarith [hx, abs_nonneg b]
            _ = _ := by ring
        -- and since it's continuous, must exist y0 such that f(y0) = 0.
        apply intermediate_value_univ₂ ?_ ?_ hy1 hy2
        · simp only [f_def]
          apply Continuous.add ?_ continuous_const
          apply Continuous.add (continuous_pow 3) (continuous_mul_left _)
        · simp [g_def, continuous_const]
      use y
    -- since y satisfy y^3+xy-x^3 = 0, we have f(a+b) = 2f(a) + f(b-a)
    have hy': y^3 + x*y = b := by linarith [hy]
    -- use h1
    have := h1 x y
    rw [← hx, ← hy', ← add_assoc, this]
  -- therefore f (x+y) = f(x) + f (y)
  have hfadd(x y: ℝ): f (x+y) = f x + f y := by
    -- take (x,y) and (y,x)
    have hh1 := h2 x y
    have hh2 := h2 y x
    -- add these terms
    have: 2* f (x+y) = 2 * (f x + f y) := by
      rw [two_mul]; nth_rw 1 [add_comm x y]
      rw [hh1, hh2]
      have: f (x-y) = - f (y-x) := by
        rw [hfnx (x-y)]; congr
        simp
      rw [this]; ring
    linarith [this]
  -- combine with f(x^3) = x^2 f(x), we can solve f(x) = xf(1)
  -- take x+1 and x-1 in f(x^3) = x^2f(x)
  intro x
  have hh1 := hfpx (x+1)
  have hh2 := hfpx (x-1)
  -- sum them up
  have: f (2 * (x^3+3*x)) = (2*x^2+2) * f x + 4*x*f 1 := by
    have: 2*(x^3+3*x) = (x+1)^3 + (x-1)^3 := by ring
    -- f (x+y) = f(x) + f(y)
    rw [this, hfadd ((x+1)^3) ((x-1)^3), hh1, hh2]
    -- f(x+1) = f(x) + f(1), f(x-1) = f(x) - f(1)
    replace: f (x-1) = f x - f 1 := by
      have: x-1 = x + -1 := by ring
      simp [this, hfadd x (-1), hfnx 1]
    rw [this, hfadd x 1]; ring
  -- f (2x) = 2 f(x)
  rw [two_mul, hfadd (x^3+3*x) _] at this
  simp only [hfadd (x^3) (3*x), hfpx x] at this
  -- f(3x) = 3 f(x)
  have hh3: f (3*x) = 3* f x := by
    have: 3*x = x+x+x := by ring
    rw [this, hfadd _ x, hfadd x]; ring
  rw [hh3] at this
  -- done
  linarith [this]