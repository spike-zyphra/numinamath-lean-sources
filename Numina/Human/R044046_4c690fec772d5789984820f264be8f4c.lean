import Mathlib

/- ## Task $6 / 74$

It is to be proven that the validity of the relationship

$$
x+\frac{1}{x}=2 \cos y
$$

implies the validity of the relationship

$$
x^{n}+\frac{1}{x^{n}}=2 \cos (n y)
$$ -/

theorem algebra_154218 {x y : ℝ} (hx : x ≠ 0) (h : x + 1/x = 2 * Real.cos y) (n : ℕ) :
    x ^ n + 1 / x ^ n = 2 * Real.cos (n * y) := by
    -- We prove it by induction
    have ind : ∀ m : ℕ, ∀ n ≤ m+1, x ^ n + 1 / x ^ n = 2 * Real.cos (n * y) := by
      intro m
      induction' m with m hm
      -- for n = 0 or 1, it's easy to check.
      simp;
      intro n hn
      by_cases neq0 : n = 0
      rw [neq0]; simp; norm_num
      have neq1 : n = 1 := by omega
      rw [neq1]; simp_all

      -- for larger n, we use the fact that cos (n+1)y + cos (n-1)y = 2 cos ny cos y.
      intro n hn
      by_cases nlemp1 : n ≤ m+1
      apply hm; exact nlemp1
      have nemp1 : n = m + 1 + 1 := by linarith
      have eq : x ^ (n) + 1 / x ^ (n) = (x^(n-1) + 1/x^(n-1)) * (x+1/x) - (x^(n-2)+1/x^(n-2)) := by 
        have tmp : (x ^ (n - 1) + 1 / x ^ (n - 1)) * (x + 1 / x) = (x ^ n + 1 / x ^ n ) + ((x ^ (n - 2) + 1 / x ^ (n - 2))) := by
          rw [add_mul]; rw [mul_add]; rw[mul_add];
          have ek : ∃ k : ℕ , k = n-2 := by use n-2; 
          rcases ek with ⟨k, hk⟩; 
          have hhk : n = k+2 := by omega
          rw[hhk]; field_simp; ring
        linarith
      rw [eq]
      have nge2 : 2≤ n := by omega

      have tmp1 : (x ^ (n - 1) + 1 / x ^ (n - 1)) = 2 * Real.cos ((n-1)*y) := by 
        have : @HMul.hMul ℝ ℝ ℝ instHMul (↑n - 1) y  = @HMul.hMul ℝ ℝ ℝ instHMul (↑(n - 1)) y := by field_simp
        rw [this]
        apply hm (n-1); omega
      have tmp2 : (x^(n-2)+1/x^(n-2)) = 2 * Real.cos ((n-2)*y) := by 
        have : @HMul.hMul ℝ ℝ ℝ instHMul (↑n - 2) y = @HMul.hMul ℝ ℝ ℝ instHMul (↑(n - 2)) y := by field_simp
        rw [this]
        apply hm (n-2); omega
      rw [tmp1, h, tmp2]

      have tmp3 : 2 * Real.cos (↑n * y) = 2 * (Real.cos ((n-1) * y) * Real.cos (y) - Real.sin ((n-1) * y) * Real.sin (y)) := by 
        have : ↑n * y = (↑n - 1) * y + y := by ring
        rw [this, Real.cos_add] 
      have tmp4 : 2 * Real.cos ((↑n - 2) * y) = 2 * (Real.cos ((n-1)*y) * Real.cos (y) + Real.sin ((n-1) * y) * Real.sin (y)) := by 
        have : (↑n - 2) * y = (↑n - 1) * y - y := by ring
        rw [this, Real.cos_sub]
      rw [tmp3,tmp4]; ring

    apply ind n n
    linarith