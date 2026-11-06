import Mathlib

/- 8. The domain of the function $f(x)$ is $\mathbf{R}$, and for any $x_{1}, x_{2} \in \mathbf{R}$, it holds that $f\left(x_{1}+x_{2}\right)=f\left(x_{1}\right)+f\left(x_{2}\right)$. When $x \geqslant 0$, the function $f(x)$ is increasing.
(1) Prove that the function $y=-(f(x))^{2}$ is increasing on $(-\infty, 0]$ and decreasing on $[0,+\infty)$.
(2) If $f(1)=2$, and the real number $a$ satisfies the inequality $f\left(2 a^{2}-1\right)+2 f(a)-6<0$, find the range of values for $a$. -/
theorem algebra_132839 (f : ℝ → ℝ)
    (hf : ∀ x y, f (x + y) = f x + f y)
    (hmono : StrictMonoOn f (Set.Ici 0)) :
    StrictMonoOn (fun x => -f x ^ 2) (Set.Iic 0) ∧
    StrictAntiOn (fun x => -f x ^ 2) (Set.Ici 0) ∧
    (f 1 = 2 → ∀ a, f (2 * a^2 - 1) + 2 * f a - 6 < 0 ↔ a ∈ Set.Ioo (-2) 1) := by
  -- Show that f 0 = 0
  have hf0 : f 0 = 0 := by
    -- We have f 0 = f (0 + 0) = f 0 + f 0, so f 0 = 0
    specialize hf 0 0
    rw [add_zero] at hf
    linarith
  -- Show that f (-x) = -f x
  have hf_neg x : f (-x) = -f x := by
    -- We have 0 = f 0 = f (x + -x) = f x + f (-x), so f (-x) = -f x
    specialize hf x (-x)
    rw [add_neg_cancel] at hf
    linarith
  -- Prove that f is increasing for all x ∈ ℝ
  replace hmono : StrictMono f := by
    -- ℝ = (-∞, 0] ∪ [0, ∞)
    suffices StrictMonoOn f (Set.Iic 0 ∪ Set.Ici 0) by
      rw [←strictMonoOn_univ]
      convert this
      simp only [Set.Iic_union_Ici]
    -- It is enough to show that f is increasing on (-∞, 0] and f is increasing on [0, ∞).
    -- f is increasing on [0, ∞) by the assumption
    apply StrictMonoOn.union (c := 0) _ hmono isGreatest_Iic isLeast_Ici
    simp [StrictMonoOn]
    intro x hx y hy hxy
    -- we need to show that f x < f y for x < y ≤ 0
    have eq1 := hf_neg (-x)
    have eq2 := hf_neg (-y)
    rw [neg_neg] at eq1 eq2
    -- replace x with -(-x) and y with -(-y) and use the fact f (-x) = -f(x)
    rw [eq1, eq2, neg_lt_neg_iff]
    -- it is left to show that f (-y) < f (-x) which follows from the monotonicity of f on [0, ∞)
    exact hmono (by simp; linarith) (by simp; linarith) (by linarith)
  -- f x ≤ 0 for all x ≤ 0 (because f is increasing and f 0 = 0)
  have hf_nonpos {x} (hx : x ≤ 0) : f x ≤ 0 := by
    rw [←hf0]
    exact hmono.monotone hx
  -- 0 ≤ f x for all 0 ≤ x (because f is increasing and f 0 = 0)
  have hf_nonneg {x} (hx : 0 ≤ x) : 0 ≤ f x := by
    rw [←hf0]
    exact hmono.monotone hx
  constructorm* _ ∧ _
  -- show that -(f x)^2 is increasing for x ≤ 0
  · simp [StrictMonoOn]
    intro x hx y hy hxy
    -- we need to show that f y ^ 2 < f x ^ 2 when x < y ≤ 0
    -- this inequality is equivalent to |f y| < |f x|
    -- we have |f y| = -f y and |f x| = -f x (since x ≤ 0 and y ≤ 0)
    -- so it is enough to show that f x < f y which follows from the monotonicity of f
    rw [sq_lt_sq, abs_of_nonpos (hf_nonpos hy), abs_of_nonpos (hf_nonpos hx), neg_lt_neg_iff]
    exact hmono hxy
  -- show that -(f x)^2 is decreasing for 0 ≤ x
  · simp [StrictAntiOn]
    intro x hx y hy hxy
    -- we need to show that f x ^ 2 < f y ^ 2 when 0 ≤ x < y
    -- this inequality is equivalent to |f x| < |f y|
    -- we have |f x| = f x and |f y| = f y (since 0 ≤ x and 0 ≤ y)
    -- so it is enough to show that f x < f y which follows from the monotonicity of f
    rw [sq_lt_sq, abs_of_nonneg (hf_nonneg hy), abs_of_nonneg (hf_nonneg hx)]
    exact hmono hxy
  -- assume that f 1 = 2 and show that
  -- f (2 * a ^ 2 - 1) + 2 * f a - 6 < 0 iff a ∈ (-2, 1)
  · intro hf1 a
    calc
      -- rewrite the inequality as f (2 * a^2 - 1 + 2 * a) < f 3 = 6
      f (2 * a^2 - 1) + 2 * f a - 6 < 0 ↔ f ((2 * a^2 - 1) + 2 * a) < f 3 := by
          -- we have f 3 = f (2 + 1) = f 2 + f 1 = f (1 + 1) + f 1 = 3 * f 1 = 6
          have hf3 : f 3 = 6 := calc
            f 3 = f 2 + f 1 := by rw [←hf]; norm_num
            _   = f 1 + f 1 + f 1 := by nth_rw 2 [←hf]; norm_num
            _   = 6 := by norm_num [hf1]
          -- 2 * f a = f a + f a = f (a + a)
          rw [hf, hf3, show 2 * a = a + a by ring, hf, sub_neg]
          ring_nf
      -- f is increasing so f ((2 * a^2 - 1) + 2 * a) < f 3
      -- is equivalent to 2 * a^2 + 2 * a - 1 < 3
      _ ↔ 2 * a^2 + 2 * a - 1 < 3 := by
          rw [hmono.lt_iff_lt]
          ring_nf
      -- 2 * a ^ 2 + 2 * a - 1 = 2 * (a + 2) * (a - 1)
      _ ↔ 2 * (a + 2) * (a - 1) < 0 := by
          rw [←sub_neg]
          ring_nf
      -- 2 * (a + 2) * (a - 1) < 0 iff a ∈ (-2, 1)
      _ ↔ a ∈ Set.Ioo (-2) 1 := by
          rw [mul_neg_iff, Set.mem_Ioo]
          constructor <;> intro h
          · cases' h with h h
            · constructor <;> linarith
            · linarith
          · left
            constructor <;> linarith