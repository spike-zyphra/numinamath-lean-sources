import Mathlib
open Real Set
open scoped BigOperators

/- Given the function $f(x) = \log_{3}(a - 3^{x}) + x - 2$, if $f(x)$ has a root, then the range of the real number $a$ is \_\_\_\_\_\_\_\_. -/
theorem algebra_9427 {a : ℝ}:
    (∃ x, logb 3 (a - 3 ^ x) + x - 2 = 0 ∧ 0 < a - 3 ^ x) ↔ a ≥ 6 := by
  -- The question must be formulated more rigorously by requiring that a > 3 ^ x, noting that the definition of logb in LEAN: logb 3 0 = 0.
  apply Iff.intro -- Break the iff into two implications.
  . intro ⟨x, h₁, h₂⟩ -- Prove that a ≥ 6 if the equation has a root.
    -- Expand the equation.
    have h₃ : logb 3 (a - 3 ^ x) = 2 - x := by
      linarith
    have h₄ : a - 3 ^ x = 3 ^ (2 - x) := by
      calc
        a - 3 ^ x = 3 ^ (logb 3 (a - 3 ^ x)) := by rw [rpow_logb]; simp; simp; exact h₂
        _ = 3 ^ (2 - x) := by rw[h₃]
    -- Prove the simplest form of AM-GM inequality.
    have h₅ : (∀ x y : ℝ, x ^ 2 + y ^ 2 ≥ 2 * (x * y)) := by
      intro x y
      suffices _ : 0 ≤ (x - y) ^ 2 by
        nlinarith
      apply sq_nonneg
    have h_tmp₁ : (0 : ℝ) ≤ (3 : ℝ) := by
      simp
    have h_tmp₂ : (0 : ℝ) < (3 : ℝ) := by
      simp
    specialize h₅ (3 ^ (x / 2)) (3 ^ ((2 - x) / 2))
    calc
      a = 3 ^ x + 3 ^ (2 - x) := by linarith
      _ = (3 ^ (x / 2)) ^ (2 : ℝ) + (3 ^ ((2 - x) / 2)) ^ (2 : ℝ) := by rw [<-rpow_mul h_tmp₁ (x / 2) 2, <-rpow_mul h_tmp₁ ((2 - x) / 2) 2]; ring_nf
      _ ≥ 2 * (3 ^ (x / 2) * 3 ^ ((2 - x) / 2)) := by simp [h₅]
      _ = 2 * 3 ^ (x / 2 + (2 - x) / 2) := by rw[<-rpow_add h_tmp₂ (x / 2) ((2 - x) / 2)]
      _ = 6 := by ring_nf
  . intro a_ineq -- Prove that the equation has a root when a ≥ 6
    use (logb 3 ((a + √(a ^ 2 - 36)) / 2)) -- This solution is solved by quadratic equation in 3 ^ x.
    -- Boring calculations to justify that it does solve the equation.
    refine ⟨?_, ?_⟩
    . rw [rpow_logb]
      have h₁ {x : ℝ} (h_sol : x = (a + √(a ^ 2 - 36)) / 2) : logb 3 (a - x) + logb 3 x - 2 = 0 := by
        have h₂ : x ^ 2 - a * x + 9 = 0 := by
          simp only [h_sol]
          ring_nf
          rw [Real.sq_sqrt]
          ring_nf
          nlinarith
        have h₃ : x ≠ 0 := by
          nlinarith
        have h₄ : a - x = 9 * x⁻¹ := by
          calc
            a - x = (a - x) * x * x⁻¹ := by rw [mul_assoc, mul_inv_cancel₀]; ring_nf; exact h₃
            _ = (-x ^ 2 + a * x) * x⁻¹ := by ring_nf
            _ = 9 * x⁻¹ := by simp; left; linarith
        calc
          logb 3 (a - x) + logb 3 x - 2 = logb 3 (9 * x⁻¹) + logb 3 x - 2 := by rw [h₄]
          _ = logb 3 9 - logb 3 x + logb 3 x - 2 := by rw[logb_mul, logb_inv]; linarith; linarith; apply inv_ne_zero h₃
          _ = logb 3 (3 ^ (2 : ℝ)) - logb 3 x + logb 3 x - 2 := by norm_num
          _ = 0 := by rw [@logb_rpow 3 2]; linarith; linarith; linarith
      apply @h₁ ((a + √(a ^ 2 - 36)) / 2)
      linarith
      linarith
      linarith
      have h₅ : 0 ≤ √(a ^ 2 - 36) := by
        apply sqrt_nonneg
      nlinarith
    . rw[rpow_logb]
      have h₂ : √(a ^ 2 - 36) < a := by
        rw [@sqrt_lt' (a ^ 2 - 36) a]
        linarith
        linarith
      linarith
      linarith
      linarith
      have h₁ : 0 ≤ √(a ^ 2 - 36) := by
        apply sqrt_nonneg
      linarith
