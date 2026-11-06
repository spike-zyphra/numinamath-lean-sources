import Mathlib

open Filter Real

/-Find the positive constant $c_{0}$ such that the series

$$
\sum_{n=0}^{\infty} \frac{n!}{(c n)^{n}}
$$

converges for $c>c_{0}$ and diverges for $0< c< c_{0}$.-/
theorem calculus_611209 (c0 : ℝ) (c0pos : 0 < c0)
    (h1 : ∀ c > c0, Summable (fun n : ℕ => n.factorial / (c * n) ^ n))
    (h2 : ∀ c > 0, c < c0 → ¬ Summable (fun n : ℕ => n.factorial / (c * n) ^ n))
    : c0 = (exp 1)⁻¹ := by
-- Prove that for any $c$ greater than $e⁻¹$, the sum in question converges
  have h3 : ∀ c > (exp 1)⁻¹, Summable (fun n : ℕ => n.factorial / (c * n) ^ n) := by
    intro c cgt; have cpos : 0 < c := by
      suffices : 0 < (rexp 1)⁻¹
      · linarith only [this, cgt]
      positivity
  -- Apply the ratio test for positivie series `summable_of_ratio_test_tendsto_lt_one`
    apply summable_of_ratio_test_tendsto_lt_one
    · have : (c * exp 1)⁻¹ < 1 := by
        rw [inv_lt_comm₀, inv_one]
        rw [gt_iff_lt, inv_lt_iff_one_lt_mul₀] at cgt
        exact cgt; all_goals positivity
      exact this
    · simp; use 0; intros; constructor
      · positivity
      intro h; rcases h with h|_
      · simp [h] at cgt; suffices : 0 < rexp 1
        · linarith only [this, cgt]
        positivity
      assumption
  -- Simplify the expression in the limit to the limit definition of $e$, the goal follows
    push_cast; have : (fun n : ℕ => ‖(n + 1).factorial / (c * (n + 1)) ^ (n + 1)‖ / ‖n.factorial / (c * n) ^ n‖)
    = (fun n : ℕ => (c * (1 + 1 / n) ^ n)⁻¹) := by
      rw [funext_iff]; intro n; by_cases hn : n = 0
      · simp [hn]; positivity
      simp [← one_div]
      rw [one_add_div, mul_pow, div_pow]
      field_simp; repeat rw [abs_eq_self.mpr]
      rw [Nat.factorial_succ]; push_cast; ring
      all_goals positivity
    rw [this, tendsto_inv_iff₀]; apply Tendsto.const_mul
    apply tendsto_one_plus_div_pow_exp; positivity
-- Prove that for any positive $c$ less than $e⁻¹$, the sum in question diverges
  have h4 : ∀ c > 0, c < (exp 1)⁻¹ → ¬ Summable (fun n : ℕ => n.factorial / (c * n) ^ n) := by
  -- Apply the ratio test for positivie series `summable_of_ratio_test_tendsto_lt_one`
    intro c cpos clt; apply not_summable_of_ratio_test_tendsto_gt_one
    · have : 1 < (c * rexp 1)⁻¹ := by
        rw [← one_div, lt_div_iff₀, one_mul]
        rw [← one_div, lt_div_iff₀] at clt; exact clt
        all_goals positivity
      exact this
  -- Simplify the expression in the limit to the limit definition of $e$, the goal follows
    push_cast; have : (fun n : ℕ => ‖(n + 1).factorial / (c * (n + 1)) ^ (n + 1)‖ / ‖n.factorial / (c * n) ^ n‖)
    = (fun n : ℕ => (c * (1 + 1 / n) ^ n)⁻¹) := by
      rw [funext_iff]; intro n; by_cases hn : n = 0
      · simp [hn]; positivity
      simp [← one_div]
      rw [one_add_div, mul_pow, div_pow]
      field_simp; repeat rw [abs_eq_self.mpr]
      rw [Nat.factorial_succ]; push_cast; ring
      all_goals positivity
    rw [this, tendsto_inv_iff₀]; apply Tendsto.const_mul
    apply tendsto_one_plus_div_pow_exp; positivity
-- Prove that $c0$ is forced to be $e⁻¹$ by `h3` and `h4`
  by_contra! h; rw [ne_iff_lt_or_gt] at h
  rcases h with h|h
  · specialize h1 ((c0+(rexp 1)⁻¹)/2) (by linarith)
    specialize h4 ((c0+(rexp 1)⁻¹)/2) (by linarith) (by linarith)
    contradiction
  specialize h2 ((c0+(rexp 1)⁻¹)/2) (by positivity) (by linarith)
  specialize h3 ((c0+(rexp 1)⁻¹)/2) (by linarith)
  contradiction