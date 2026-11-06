import Mathlib

open Filter Real Asymptotics

/- Show that a function \( f \) is \( O\left(\log_{2} n\right) \) if and only if \( f \) is \( O\left(\log_{r} n\right) \) for any \( r > 1 \).
  (Hint: Recall that \( \frac{\log_{a} n}{\log_{b} n} = \log_{a} b \).) -/
theorem number_theory_4466 {f : ℝ → ℝ} :
    f =O[atTop] logb 2 ↔ ∃ r > 1, f =O[atTop] logb r := by
  refine ⟨fun h => ?_, fun ⟨r, hr, h⟩ => ?_⟩
  -- If f(n) = O(log2 n), then r=2 satisfies requirement.
  · use 2; simpa
  -- If there exists r such that f(n) = O(logr n), then f(n) = O(log2 n)
  · rw [← isBigO_const_mul_right_iff (c := (logb 2 r)⁻¹)]
    -- According to the fact that `f(n)=O(g(n)) → f(n)=O(c*g(n))`,
    -- we can multiple `(log2 r)⁻¹` to `logb n`.
    -- This transform `logb n` to `log2 n` which is desired.
    · rwa [isBigO_congr (EventuallyEq.refl _ _) (g₂ := logb r)]
      rw [EventuallyEq, eventually_atTop]
      use 1
      intro x _
      simp only [logb, inv_div]
      have : log r ≠ 0 := by simp; (repeat (constructor; linarith)); linarith
      field_simp
      ring
    -- Check `(log2 r)⁻¹≠0`
    · simp; (repeat (constructor; linarith)); linarith
