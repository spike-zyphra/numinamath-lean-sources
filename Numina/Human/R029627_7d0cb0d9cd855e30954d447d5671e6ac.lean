import Mathlib

open Real Finset Topology Filter

/- 15. Given the function $f(x)=a_{1} x+a_{2} x^{2}+\cdots+a_{n} x^{n}$
$\left(n \in \mathbf{N}_{+}\right), a_{1}, a_{2}, \cdots, a_{n}$ are terms of a sequence. If $f(1)=n^{2}+1$, (1) find the general term formula of the sequence $\left\{a_{n}\right\}$; (2) find $\lim _{n \rightarrow \infty}\left(1-\frac{1}{a_{n}}\right)^{n}$. -/
theorem algebra_254747 {a : ℕ → ℝ}
    (h : ∀ n > 0, ∑ i in Icc 1 n, a i = n ^ 2 + 1) :
    a 1 = 2 ∧ (∀ n ≥ 2, a n = 2 * n - 1) ∧
    Tendsto (fun n : ℕ => (1 - (1 : ℝ) / a n)^n) atTop (𝓝 (Real.exp (-1 / 2))) := by
  -- ∑ i ∈ [1, 1], a i = 1^2 + 1 implies that a(1) = 2.
  have ha1 : a 1 = 2 := by
    have := h 1 (by norm_num)
    simp at this
    norm_num [this]
  -- Show that a(n) = 2 * n - 1 for n ≥ 2.
  have ha : ∀ n ≥ 2, a n = 2 * n - 1 := by
    intro n hn
    have h1 := h (n - 1 + 1) (by linarith)
    -- We have n^2 + 1 = ∑ i ∈ [1, n], a i = ∑ i ∈ [1, n - 1], a i + a n = (n - 1)^2 + 1 + a n.
    rw [Finset.sum_Icc_succ_top (by linarith)] at h1
    rw [h (n - 1) (by omega), show n - 1 + 1 = n by omega] at h1
    push_cast [show n ≥ 1 by omega] at h1
    -- It follows that a(n) = n^2 + 1 - (n - 1)^2 - 1 = 2 * n - 1.
    linear_combination h1
  refine ⟨ha1, ha, ?_⟩
  -- Show that lim (1 - 1 / a(n))^n = exp(-1/2) as n tends to infinity.
  -- We have (1 - 1 / a(n))^n = (1 + (-1) / n)^n / (1 + (-1 / 2) / n)^n for n ≥ 2.
  have eq1 : (fun n : ℕ => ((1 + -1 / (n : ℝ))^n / (1 + (-1 / 2) / (n : ℝ))^n)) =ᶠ[atTop] (fun n : ℕ => (1 - (1 : ℝ) / a n)^n) := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    use 2
    intro n hn
    rw [ha n hn, ← div_pow]
    congr
    rify at hn
    field_simp [show 2 * (n : ℝ) - 1 ≠ 0 by linarith, show 2 * (n : ℝ) + (-1) = 2 * n - 1 by ring]
    ring
  -- It is enough to show that lim ((1 + (-1) / n)^n / (1 + (-1 / 2) / n)^n) = exp(-1/2).
  apply Filter.Tendsto.congr' eq1
  -- exp(-1/2) = exp(-1) / exp(-1/2).
  have eq2 : exp (-1 / 2) = exp (-1) / exp (-1 / 2) := by
    rw [← exp_sub, show - 1 - (-1 / 2 : ℝ) = -1 / 2 by norm_num]
  rw [eq2]
  -- The result follows from the fact that the limit of (1 + x/n)^n = exp(x) for any real x
  apply Tendsto.div _ _ (by positivity)
  · exact tendsto_one_plus_div_pow_exp (-1)
  · exact tendsto_one_plus_div_pow_exp (-1 / 2)