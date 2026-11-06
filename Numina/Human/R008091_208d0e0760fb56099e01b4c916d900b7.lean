import Mathlib

/-Given the function $f(x)=\sin x+a\cos x$ where $(a \lt 0)$ has a maximum value of $2$,
then $f(\frac{π}{6})=\_\_\_\_\_\_$.-/
theorem algebra_9422 {a : ℝ} (ha : a < 0) (f : ℝ → ℝ) (hf : f = fun x => Real.sin x + a * Real.cos x)
    (hmax : IsGreatest (Set.range f) 2) :
    f (Real.pi / 6) = -1 := by
  -- 1. Upper Bound of \( f(x) \):
  -- Using the Cauchy-Schwarz inequality, we know:
  -- \[\sin(x) + a \cdot \cos(x) \leq \sqrt{1^2 + a^2}.\]
  -- Therefore, for any \( x \in \mathbb{R} \), \( f(x) \leq \sqrt{1 + a^2} \).
  have fleq : ∀ x : ℝ, f x ≤ Real.sqrt (1 + a ^ 2) := by
    have ineq (a b c d : ℝ) :  a * c + b * d ≤ Real.sqrt ((a ^ 2 + b ^ 2)) * Real.sqrt (c ^ 2 + d ^ 2) := by
        suffices a * c + b * d ≤ Real.sqrt ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) by
            rwa [Real.sqrt_mul (by linarith [sq_nonneg a, sq_nonneg b])] at this
        apply Real.le_sqrt_of_sq_le
        apply le_of_sub_nonpos
        have {x y : ℝ} : x - y ≥ 0 ↔ y - x ≤ 0 := by simp only [ge_iff_le, sub_nonneg, tsub_le_iff_right, zero_add]
        rw [← this]
        calc
        _ = (a * d - b * c) ^ 2 := by ring
        _ ≥ 0 := sq_nonneg (a * d - b * c)
    have {x : ℝ} := ineq 1 a (Real.sin x) (Real.cos x)
    simpa only [hf, one_mul, one_pow, Real.sin_sq_add_cos_sq, Real.sqrt_one, mul_one]
  -- 2. Achieving Maximum Value:
  -- To achieve the maximum \( f(x) = \sqrt{1 + a^2} \), set
  -- \[x = \frac{\pi}{2} - \arctan(a).\]
  -- Calculations confirms that \( \sqrt{1 + a^2} \) is the maximum value.
  have fmax : IsGreatest (Set.range f) (Real.sqrt (1 + a ^ 2)) := by
    constructor
    · simp only [hf, Set.mem_range]
      use (Real.pi/2 - Real.arctan (a))
      simp [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, Real.sin_arctan, Real.cos_arctan]
      field_simp
      exact (pow_two a).symm
    · simpa only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  -- 3. Solve for a:
  -- Since the problem states that the maximum value of \( f(x) \) is 2, we have:
  -- \[\sqrt{1 + a^2} = 2.\]
  -- Squaring both sides:
  -- \[ 1 + a^2 = 4 \quad \Rightarrow \quad a^2 = 3.\]
  -- Therefore, \( a = \pm \sqrt{3} \). Given \( a < 0 \), it follows that \( a = -\sqrt{3} \).
  have : a = - (Real.sqrt 3) := by
    have eq := IsGreatest.unique fmax hmax
    rw [Real.sqrt_eq_iff_eq_sq (by linarith [sq_nonneg a]) (by norm_num)] at eq
    replace eq : a ^ 2 = (Real.sqrt 3) ^ 2 := by linarith [@Real.sq_sqrt 3 (by norm_num)]
    obtain rfl | rfl := eq_or_eq_neg_of_sq_eq_sq a (Real.sqrt 3) eq
    · absurd ha
      norm_num
    · rfl
  -- 4. Value at \( x = \pi/6 \):
  field_simp [hf, this]
  norm_num