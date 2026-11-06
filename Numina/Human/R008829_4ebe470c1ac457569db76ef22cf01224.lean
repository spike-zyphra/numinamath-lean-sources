import Mathlib

/- 1. The numerical sequence $\left\{a_{n}\right\}_{n=1}^{\infty}$ is defined such that $a_{1}=\log _{2}\left(\log _{2} f(2)\right), \quad a_{2}=$ $\log _{2}\left(\log _{2} f(f(2))\right), \ldots, a_{n}=\log _{2}(\log _{2} \underbrace{f(f(\ldots f}_{n}(2)))), \ldots$, where $f(x)=x^{x}$. Determine the index $n$ for which $a_{n}=2059+2^{2059}$.  -/

theorem algebra_264873 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ x) (a : ℕ → ℝ)
    (ha : ∀ n, a n = Real.logb 2 (Real.logb 2 (f^[n] 2))) :
    ∃ n, a n = 2059 + 2 ^ 2059 := by

  -- We need to prelimiarly show that the function f is positive
  have fpos {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 < f^[n] x := by
    induction' n with n ih generalizing x
    · exact hx
    · rw [Function.iterate_succ, Function.comp_apply, hf]
      exact ih (Real.rpow_pos_of_pos hx x)

  -- And that x <= f(x) for all x >= 1
  have fpos' {x : ℝ} (hx : 1 <= x) (n : ℕ) : x <= f^[n] x := by
    induction' n with n ih generalizing x
    · simp
    · rw [Function.iterate_succ, Function.comp_apply, hf]
      apply le_trans (Real.self_le_rpow_of_one_le hx hx)
      exact ih (le_trans hx (Real.self_le_rpow_of_one_le hx hx))

  -- Now we prove that a n satisfies the recurrence relation a (n + 1) = a n + 2 ^ (a n).
  have (n : ℕ) : a (n + 1) = a n + 2 ^ (a n) := by
    rw [ha, Function.iterate_succ', Function.comp_apply]
    have := (ha n).symm
    rw [Real.logb_eq_iff_rpow_eq (by linarith) (by linarith) (by
      apply Real.logb_pos (by linarith) (by
      apply lt_of_lt_of_le (by linarith : (1 : ℝ) < 2) (fpos' (by linarith) n)))] at this
    symm at this
    rw [Real.logb_eq_iff_rpow_eq (by linarith) (by linarith) (fpos (by linarith) n)] at this
    rw [← this, hf]
    rw [Real.logb_rpow_eq_mul_logb_of_pos (by rw [this]; exact fpos (by linarith) n)]
    rw [Real.logb_mul (by rw [this]; exact Ne.symm (ne_of_lt (fpos (by linarith) n))) (by
        rw [Real.logb_rpow]; intro h
        rw [Real.rpow_eq_zero_iff_of_nonneg (by linarith)] at h; obtain ⟨h, _⟩ := h; all_goals linarith)]
    rw [this, ← (ha n)]
    rw [← Real.logb_eq_iff_rpow_eq (by linarith) (by linarith) (fpos (by linarith) n)] at this
    rw [this, add_comm]

  -- It is enough to show that a 4 = 2059; we do it step by step.
  use 5; rw [this]
  suffices a 4 = 2059 by rw [this]; exact_mod_cast rfl
  rw [this, (by norm_num : (2059 : ℝ) = 11 +  2 ^ 11)]
  suffices a 3 = 11 by rw [this]; exact_mod_cast rfl
  rw [this, (by norm_num : (11 : ℝ) = 3 + 2 ^ 3)]
  suffices a 2 = 3 by rw [this]; exact_mod_cast rfl
  rw [this, (by norm_num : (3 : ℝ) = 1 + 2 ^ 1)]
  suffices a 1 = 1 by rw [this]; exact_mod_cast rfl
  rw [this, (by norm_num : (1 : ℝ) = 0 + 2 ^ 0)]
  suffices a 0 = 0 by rw [this]; exact_mod_cast rfl
  simp [ha]