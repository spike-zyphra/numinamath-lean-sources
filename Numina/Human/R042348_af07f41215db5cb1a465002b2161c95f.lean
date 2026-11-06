import Mathlib

/- Example 13 Let $a, b, c$ be positive real numbers, and $abc=1$. Prove that $\frac{1}{a^{3}(b+c)}+\frac{1}{b^{3}(c+a)}+\frac{1}{c^{3}(a+b)} \geqslant \frac{3}{2}$. -/
theorem inequalities_252723 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 / 2 ≤ 1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (c + a)) + 1 / (c ^ 3 * (a + b)) := by
  -- We have the following equality for all positive x, y, z such that x * y * z = 1:
  -- 1 / (x^3 * (y + z)) = (y * z)^2 / (x * y + x * z).
  have heq {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1) :
        1 / (x ^ 3 * (y + z)) = (y * z) ^ 2 / (x * y + x * z) := calc
    -- We have 1 = x * y * z and multiply numerator and denominator by y * z.
    1 / (x ^ 3 * (y + z)) = (x * y * z) * (y * z) / ((x ^ 3 * (y + z)) * (y * z)) := by
        rw [h, mul_div_mul_right _ _ (by apply ne_of_gt; positivity)]
    -- We get
    --x * (y * z)^2 / (x * (x * y * z * (x * y) + x * y * z * (x * z))).
    _ = x * (y * z)^2 / (x * (x * y * z * (x * y) + x * y * z * (x * z))) := by
        congr 1 <;> ring
    -- Cancel x > 0 and replace x * y * z with 1 to get the result.
    _ = (y * z)^2 / (x * y + x * z) := by
        rw [h, mul_div_mul_left _ _ (by linarith), one_mul, one_mul]
  -- Using the equality heq we rewrite the goal as follows:
  -- 3 / 2 ≤ (b * c) ^ 2 / (a * b + a * c) + (c * a) ^ 2 / (b * c + b * a) + (a * b) ^ 2 / (c * a + c * b).
  rw [heq ha hb hc habc, heq hb hc ha (by linear_combination habc), heq hc ha hb (by linear_combination habc)]
  -- Let s = a * b + b * c + c * a.
  set s := a * b + b * c + c * a
  -- Let f(x) = x ^ 2 / (s - x).
  set f : ℝ → ℝ := fun x => x ^ 2 / (s - x)
  -- Define auxiliary functions w and p as follows:
  -- w(i) = 1 / 3, p(0) = b * c, p(1) = c * a, p(2) = a * b.
  set w : ℕ → ℝ := fun _ => 1 / 3
  set p : ℕ → ℝ := fun i => if i = 0 then b * c else if i = 1 then c * a else a * b
  -- Show that f is convex on (0, s).
  have hf : ConvexOn ℝ (Set.Ioo 0 s) f := by
    -- The first derivative of f is (2 * s * x - x ^ 2) / (s - x) ^ 2 for x ∈ (0, s).
    have hdf x (hx : x ∈ Set.Ioo 0 s) : HasDerivAt f (((2 * x ^ 1) * (s - x) - x ^ 2 * (0 - 1)) / (s - x) ^ 2) x := by
      simp only [Set.mem_Ioo] at hx
      apply HasDerivAt.div _ _ (by linarith)
      · apply hasDerivAt_pow
      · apply HasDerivAt.sub (hasDerivAt_const x s) (hasDerivAt_id' x)
    -- Prove that the derivative of f is equal to (2 * s * x - x ^ 2) / (s - x) ^ 2 on
    -- an open neighborhood of x ∈ (0, s).
    have hd x (hx : x ∈ Set.Ioo 0 s) : deriv f =ᶠ[nhds x] fun x => (2 * s * x - x ^ 2) / (s - x) ^ 2 := by
      apply Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hx)
      intro y hy
      rw [(hdf y hy).deriv]
      ring
    -- Compute the second derivative of f for x ∈ (0, s).
    -- We get f''(x) = ((2 * s - 2 * x) * (s - x) ^ 2 + (2 * s * x - x ^ 2) * (2 * (s - x))) / ((s - x) ^ 2) ^ 2.
    have hd2f x (hx : x ∈ Set.Ioo 0 s) : HasDerivAt (deriv f) (((2 * s * 1 - 2 * x ^ 1) * (s - x) ^ 2 - (2 * s * x - x ^ 2) * (2 * (s - x) ^ 1 * (0 - 1))) / ((s - x) ^ 2) ^ 2) x := by
      apply HasDerivAt.congr_of_eventuallyEq _ (hd x hx)
      simp only [Set.mem_Ioo] at hx
      apply HasDerivAt.div
      · apply HasDerivAt.sub
        · apply HasDerivAt.const_mul _ (hasDerivAt_id' x)
        · apply hasDerivAt_pow
      · apply HasDerivAt.pow
        apply HasDerivAt.sub (hasDerivAt_const x s) (hasDerivAt_id' x)
      · apply ne_of_gt
        nlinarith
    -- Now we can prove that f is convex on (0, s) by showing that its second derivative is nonnegative.
    apply convexOn_of_deriv2_nonneg' (convex_Ioo 0 s)
    · intro x hx
      exact (hdf x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hd2f x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      simp [(hd2f x hx).deriv]
      apply div_nonneg _ (by positivity)
      -- Rewrite f''(x) as 2 * (s - x) * ((s - x) ^ 2 + x * (2 * s - x)).
      -- This expression is nonnegative because 0 < x < s.
      rw [show (2 * s - 2 * x) * (s - x) ^ 2 + (2 * s * x - x ^ 2) * (2 * (s - x)) = 2 * (s - x) * ((s - x) ^ 2 + x * (2 * s - x)) by ring]
      simp only [Set.mem_Ioo] at hx
      apply mul_nonneg (by linarith)
      nlinarith
  -- Show that
  -- 3 / 2 ≤ (b * c) ^ 2 / (a * b + a * c) + (c * a) ^ 2 / (b * c + b * a) + (a * b) ^ 2 / (c * a + c * b).
  -- Observe that the right hand side of this inequality can be written as
  -- 3 * ∑ i ∈ Finset.range 3, w i * f (p i).
  -- The result will follow from Jensen's inequality applied to the convex function f.
  calc
    -- We have 3 / 2 = 1 / 2 * 3 * 1 = 1 / 2 * 3 * ((a * b * c) ^ 2) ^ (1 / 3).
    3 / 2 = 1 / 2 * 3 * ((a * b * c) ^ 2) ^ (1 / 3 : ℝ) := by
        rw [habc, one_pow, Real.one_rpow]
        norm_num
    -- (a * b * c) ^ 2 = (a * b) * (b * c) * (c * a).
    _ = 1 / 2 * 3 * ((a * b) ^ (1 / 3 : ℝ) * (b * c) ^ (1 / 3 : ℝ) * (c * a) ^ (1 / 3 : ℝ)) := by
        congr
        rw [show (a * b * c) ^ 2 = (a * b) * (b * c) * (c * a) by ring]
        repeat rw [Real.mul_rpow (by positivity) (by positivity)]
    -- Apply the AM-GM inequality to (a * b), (b * c), (c * a) and get
    -- (a * b)^(1/3) * (b * c)^(1/3) * (c * a)^(1/3) ≤ 1/3 * ((a * b) + (b * c) + (c * a)).
    _ ≤ 1 / 2 * 3 * ((1 / 3) * (a * b) + (1 / 3) * (b * c) + (1 / 3) * (c * a)) := by
        gcongr
        exact Real.geom_mean_le_arith_mean3_weighted (by norm_num) (by norm_num) (by norm_num)
                (by positivity) (by positivity) (by positivity) (by norm_num)
    -- (a * b) + (b * c) + (c * a) = s.
    _ = 1 / 2 * s := by ring
    -- Show that 3 * f (s / 3) = s / 2.
    _ = 3 * f (s / 3) := by
        dsimp [f]
        have : s * 3 - s ≠ 0 := by
          apply ne_of_gt
          rw [show s * 3 - s = 2 * s by ring]
          positivity
        field_simp [this]
        ring
    -- f (s / 3) = f ((b * c) / 3 + (c * a) / 3 + (a * b) / 3) = f (∑ i ∈ [0, 2], w(i) * p(i)).
    _ = 3 * f (∑ i ∈ Finset.range 3, w i * p i) := by
        simp [Finset.sum_range_succ, w, p, s]
        ring
    -- Apply Jensen's inequality to f and get
    -- f (∑ i ∈ [0, 2], w(i) * p(i)) ≤ ∑ i ∈ [0, 2], w(i) * f(p(i)).
    _ ≤ 3 * (∑ i ∈ Finset.range 3, w i * f (p i)) := by
        gcongr
        apply hf.map_sum_le (by simp [w]) (by simp [w])
        intro i hi
        simp only [Set.mem_Ioo, p]
        constructor
        · split_ifs <;> positivity
        · split_ifs <;> (simp [s]; nlinarith)
    -- We get the final result from
    -- ∑ i ∈ [0, 2], w(i) * f(p(i)) = (b * c) ^ 2 / (a * b + a * c) + (c * a) ^ 2 / (b * c + b * a) + (a * b) ^ 2 / (c * a + c * b).
    _ = (b * c) ^ 2 / (a * b + a * c) + (c * a) ^ 2 / (b * c + b * a) + (a * b) ^ 2 / (c * a + c * b) := by
        simp [Finset.sum_range_succ, w, mul_add, p, f]
        ring