import Mathlib

open Real Set
open scoped BigOperators

/-
The function $f(x) = \log_a(6-ax)$ is decreasing on the interval $(0,2)$. The range of values for $a$ is \_\_\_\_\_\_.
-/
theorem algebra_9161 {a : ℝ} (ha : 0 < a ∧ a ≠ 1) :
    (∀ x ∈ Ioo 0 2, (0 < 6 - a * x ∧ deriv (λ x => logb a (6 - a * x)) x < 0)) →
    1 < a ∧ a ≤ 3 := by
    intro h
    constructor
    · -- First, we prove 1 < a
      -- We use proof by contradiction, assuming $a \le 1$ and deriving a contradiction.
      by_contra h'
      -- Clearly, based on the given conditions, $a < 1$.
      have h' : a < 1 := by
        simp at h'
        exact lt_of_le_of_ne h' ha.2
      -- Also, $0 < 6 - a$ and the derivative of $f(x) = \log_a(6 - a * x)$ at x is less than 0.
      obtain ⟨ht, h1⟩ := h 1 (by simp)
      dsimp [Real.logb] at h1
      -- Clearly, log a ≠ 0
      have hloga_ne_zero : log a ≠ 0 := Real.log_ne_zero.mpr ⟨by linarith, ha.2, by linarith⟩
      rw [deriv_div] at h1
      have hloga_pos : log a < 0 := (Real.log_neg_iff ha.1).mpr h'
      simp_all
      rw [show log a ^ 2 = log a * log a by linarith] at h1
      rw [mul_div_mul_right _ _  (show log a ≠ 0 by linarith)] at h1
      rw [div_lt_iff_of_neg hloga_pos, zero_mul] at h1
      -- Then, using the derivative formula for the logarithm function, we can conclude that the derivative of f(x) = log(6 - a * x) at 1 is greater than 0.
      have : (fun x ↦ log (6 - a * x)) = log ∘ fun x ↦ 6 - a * x := by rfl
      rw [this, Real.deriv_log_comp_eq_logDeriv,logDeriv.eq_1] at h1
      -- That is, the derivative of f(x) = 6 - a * x at 1 is greater than 0.
      simp_all
      have : 0 < 6 - a := by linarith
      rw [deriv_const_sub,deriv_const_mul,deriv_id''] at h1
      -- Therefore, a < 0, contradicting 0 < a. Thus, 1 < a holds.
      simp_all;
      linarith [ha.1,h1]
      simp_all
      apply (DifferentiableAt.sub_iff_right _).mpr
      apply DifferentiableAt.const_mul (by simp)
      simp_all
      linarith
      apply DifferentiableAt.log
      apply (DifferentiableAt.sub_iff_right _).mpr
      apply DifferentiableAt.const_mul (by simp)
      simp_all
      linarith
      apply DifferentiableAt.log
      simp_all; linarith
      exact hloga_ne_zero
    · -- Next, we prove a ≤ 3
      -- Similarly, we use proof by contradiction, assuming 3 < a and deriving a contradiction.
      by_contra h'
      simp at h'
      -- According to the problem conditions, clearly for any x ∈ (0, 2), $a < 6 / x$
      have h : ∀ x ∈ Ioo 0 2, a < 6 / x := by
        intro x hx
        exact (lt_div_iff (show 0 < x by linarith [hx.1])).mpr (by linarith [h x hx])
      -- Therefore, for any y ∈ (3, ∞), $a < y$
      have h : ∀ x ∈ Set.Ioi 3, a < x := by
        intro y hy
        have : 6 / y ∈ Ioo 0 2 := by
          simp_all
          constructor
          · linarith
          · apply (div_lt_iff (by linarith)).mpr
            linarith
        have := h (6/y) this
        rw [div_div_cancel' (show (6 : ℝ) ≠ 0 by linarith)] at this
        exact this
      -- But this contradicts 3 < a. Hence, a ≤ 3 holds.
      linarith [h a (by simp [h'])]
    -- The proof of the original proposition is complete.
