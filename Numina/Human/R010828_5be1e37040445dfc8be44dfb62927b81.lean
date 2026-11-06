import Mathlib

open Real

/-- Let $x_{0}=10^{9}, x_{n}=\frac{x_{n-1}^{2}+2}{2 x_{n-1}}$.
    Prove that $0<x_{36}-\sqrt{2}<10^{-9}$. -/
theorem algebra_284698 (x : ℕ → ℝ) (hx0 : x 0 = 10 ^ 9)
    (hxn : ∀ n, x (n + 1) = ((x n) ^ 2 + 2) / (2 * x n)) :
    0 < x 36 - sqrt 2 ∧ x 36 - sqrt 2 < 10 ^ (-9 : ℤ) := by
  -- We show inductively that $0 < x_n - \sqrt 2$.
  have pos (n) : 0 < x n - √2 := by
    induction n with
    -- n = 0 is clear.
    | zero => rw[hx0, sub_pos, sqrt_lt] <;> linarith
    | succ n ind =>
    -- For n + 1, rewrite $x_{n+1} - \sqrt{2} = \frac{x_n^2 + 2 - \sqrt 2 2 x_n}{2 x_n}$
        rw[hxn]
        have : 0 < x n := by trans x n - √ 2; assumption; simp
        convert_to 0 < (x n - √2)^2/(2 * x n)
        -- which equals $\frac{(x-2)^2}{2x_n}$, hence is positive by the induction hypothesis.
        · rw[sub_sq, sq_sqrt (by simp)]
          have : (2 * x n * √2) / (2 * x n) = √2 := by rw[div_eq_iff]; ring; positivity
          conv => lhs; rw[← this]
          ring
        · positivity
  -- In particular, all $x_n$ are positive.
  have pos' (n) : 0 < x n := by trans x n - √ 2; apply pos; simp
  have expand n : (2 * x n * √2) / (2 * x n) = √2 := by rw[div_eq_iff]; ring; specialize pos' n; positivity
  -- Since x > 1, this also gets us the estimate $x_{n+1} - \sqrt{2} < (x_n - \sqrt 2)^2 / 2$.
  have step (n) : x (n+1) - √ 2 < (x n - √ 2)^2 / 2 := by
    rw[sub_sq, hxn, sq_sqrt (by simp)]
    conv => lhs; rw[← expand n, ← sub_div]; lhs; lhs; rhs; rw[← sq_sqrt (x := 2) (by simp)]
    conv => rhs; lhs; rhs; rw[← sq_sqrt (x := 2) (by simp)]
    rw[div_lt_div_iff₀]
    · convert_to 2 * (x n - √2)^2 < (x n - √2)^2 * (2 * x n)
      · ring
      · ring
      · specialize pos n
        conv => lhs; rw[mul_comm 2]; rhs; rw[← mul_one 2]
        gcongr
        trans √ 2
        · convert_to √ 1 < √ 2
          · simp
          · apply sqrt_lt_sqrt (by simp) (by simp)
        · simpa using pos
    · specialize pos' n; positivity
    · simp
  -- Now we show inductively that $x_n - \sqrt 2 < x_0/2^n$.
  have estimate (n) : x n - √ 2 < x 0 / 2^n := by
    -- n = 0 is clear.
    induction n with
    | zero => simp
    | succ n ind =>
      -- For the induction step n+1, rewrite to $\frac{(x_n - \sqrt 2)^2}{2 x_n} < x_0/2^{n+1}$,
      -- or alternatively, using the induction hypothesis, $\frac{(x_n - \sqrt 2)^2}{x_n} < x_n$.
      -- This holds precisely if $(x_n - \sqrt 2)^2 < x_n^2$, which is true by positivity of the former.
        rw[hxn]
        trans (x n - √2)/2
        · conv => lhs; rw[← expand n, ← sub_div]
          rw[div_lt_div_iff₀]
          convert_to (x n - √2)^2 * 2 < _
          · conv => lhs; lhs; lhs; rhs; rw[← sq_sqrt (x := 2) (by simp)]
            ring
          · rw[sq, mul_assoc]
            rw[mul_lt_mul_left]
            rw[← sub_pos]
            convert_to 0 < 2 * √2
            · ring
            · positivity
            · apply pos
          · specialize pos' n; positivity
          · simp
        · rw[div_lt_div_iff₀ (by positivity) (by positivity)]
          rw[← mul_lt_mul_right (a := 2^(n+1)) (by positivity)] at ind
          field_simp at ind
          rw[mul_div_assoc] at ind
          convert ind using 2
          · rw[div_eq_mul_inv, ← pow_sub₀] <;> simp
  have ismono : StrictMonoOn (fun a : ℝ => a^2 / 2) (Set.Ioi 0) := by
    intro x hx y hy h
    simp only
    apply div_lt_div₀
    apply pow_lt_pow_left₀ h hx.le (by simp)
    · rfl
    · positivity
    · simp

  apply And.intro $ pos 36
  specialize estimate 30
  -- For n = 30, we can see that $x_{30} - \sqrt 2 < x_0/2^30 < 1$.
  rw[hx0] at estimate
  have : (10:ℝ)^9/2^30 < 1 := by norm_num
  replace estimate := estimate.trans this
  -- Now we apply the estimate $x_{n+1} - \sqrt{2} < (x_n - \sqrt 2)^2 / 2$ a bunch of times for
  -- $x_{31} - \sqrt{2} < 1/2$,
  have : x 31 - √ 2 < 1/2 := by
    have := (step 30).trans (ismono (pos 30) (by simp) estimate)
    simp only at this
    convert this
    norm_num
  -- $x_{32} - \sqrt{2} < 1/8$,
  have : x 32 - √ 2 < 1/8 := by
    have := (step 31).trans (ismono (pos 31) (by simp) this)
    simp only at this
    convert this using 1
    norm_num
  -- $x_{33} - \sqrt{2} < 1/2^7$,
  have : x 33 - √ 2 < 1/2^7 := by
    have := (step 32).trans (ismono (pos 32) (by simp) this)
    simp only at this
    convert this using 1
    norm_num
  -- $x_{34} - \sqrt{2} < 1/2^{15}$,
  have : x 34 - √ 2 < 1/2^15 := by
    have := (step 33).trans (ismono (pos 33) (by simp) this)
    simp only at this
    convert this using 1
    norm_num
  -- $x_{35} - \sqrt{2} < 1/2^{31}$,
  have : x 35 - √ 2 < 1/2^31 := by
    have := (step 34).trans (ismono (pos 34) (by simp) this)
    simp only at this
    convert this using 1
    norm_num
  -- and finally $x_{36} - \sqrt{2} < 1/2^{63}$, which is smaller than 10^9, as desired.
  have : x 36 - √ 2 < 1/2^63 := by
    have := (step 35).trans (ismono (pos 35) (by simp) this)
    simp only at this
    convert this using 1
    norm_num
  apply this.trans
  norm_num