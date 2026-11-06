import Mathlib

/- We claim that $f$ in the statement is non-negative. -/
lemma lemma_1 {f : ℝ → ℝ} (hf : ∀ x y : ℝ, f (x + y) = f x * f y) (x : ℝ) : 0 ≤ f x := by
  -- We take $\frac{x}{2}$ and $\frac{x}{2}$ in the given functional equation.
  -- So we get $f(x) = f(\frac{x}{2})^2 \geq 0$.
  specialize hf (x / 2) (x / 2)
  simp only [add_halves] at hf
  exact hf ▸ mul_self_nonneg (f (x / 2))

lemma lemma_2 {f : ℝ → ℝ} (hf : ∀ x y : ℝ, f (x + y) = f x * f y) (x : ℝ) (n : ℕ) (hn : 1 ≤ n) : f (n * x) = f x ^ n := by
  -- We prove this by induction on $n$.
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih => simp [add_one_mul, hf, ih, pow_succ] -- Simplify using the functional equation and the induction hypothesis

/- $f$ is a continuous real-valued function such that $f(x+y)=f(x) f(y)$ for all real $x, y$. If $f(2)=5$, find $f(5)$. -/
theorem algebra_170356 (f : ℝ → ℝ) (hfcont : Continuous f) (hf : ∀ x y : ℝ, f (x + y) = f x * f y) (h : f 2 = 5) :
    f 5 = 25 * √5 := by
  -- We can compute $f(1)$.
  -- $f(2) = f(1) ^ 2 = 5$
  have h₁ := lemma_2 hf 1 2 (by simp)
  simp only [Nat.cast_ofNat, mul_one, h] at h₁
  -- Since $f$ is non-negative, we have $f(1) = \sqrt{5}$.
  replace h₁ : f 1 = √5 := (((Real.sqrt_eq_iff_eq_sq (by simp) (lemma_1 hf 1)).mpr) h₁).symm
  -- We can compute $f(5)$.
  -- $f(5) = f(1) ^ 5 = (\sqrt{5})^5 = 25 \sqrt{5}$
  have h₂ := lemma_2 hf 1 5 (by simp)
  simp only [Nat.cast_ofNat, mul_one, h₁] at h₂
  calc f 5
    _ = √5 ^ 5 := h₂
    _ = (√5 ^ 2) ^ 2 * √5 := by ring
    _ = 25 * √5 := by norm_num
