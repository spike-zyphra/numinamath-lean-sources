import Mathlib

open Real Set

theorem algebra_608518 :
  logb 2008 2009 > logb 2009 2010 := by
    rw [logb, logb]
    -- we set y = log(x+1)/log(x), so logb 2008 2009 = y 2008 and logb 2009 2010 = y 2009
    let y := λ x => log (x + 1) / log (x)

    -- prove y is strictly decreasing on (1, +∞) by derivative
    have h1: StrictAntiOn y (Ioi 1) := by
      let y' := λ x => (log x * x - (x+1) * log (x+1) ) / ((x+1)*x*(log x)^2)

      have hy':  ∀ x: ℝ, 1 < x → HasDerivAt y (y' x) x := by
        intro x hx
        have h1 : HasDerivAt (λ x => log (x + 1)) (1 / (x + 1)) x := by
          apply HasDerivAt.log
          exact hasDerivAt_id x |>.add_const 1
          linarith
        have h2 : HasDerivAt (λ x => log x) (1 / x) x := by
          apply HasDerivAt.log
          exact hasDerivAt_id x
          linarith
        have h3 : HasDerivAt (λ x => log (x + 1) / log x) (y' x) x := by
          unfold y'
          have h4 := log_pos hx
          have h5 := HasDerivAt.div h1 h2 (by linarith)
          field_simp [h1.deriv, h2.deriv, hx]  at h5
          exact h5
        exact h3

      -- prove y' < 0 on (1, +∞)
      have hy'_pos : ∀ x: ℝ, 1 < x → y' x < 0 := by
        intro x hx
        unfold y'
        have h1: 0 < log x := by
          apply log_pos
          linarith
        have h2: 0 < ((x + 1) * x * log x ^ 2) := by positivity
        rw [div_lt_iff₀ h2]
        field_simp
        rw [mul_comm]
        have h3: x < (x+1) := by linarith
        have h4: log x < log (x+1) := by
          exact log_lt_log (by linarith) h3
        calc x * log x < x * log (x+1) := by rw [mul_lt_mul_left]; all_goals linarith
          _ < (x+1) * log (x+1) := by rw [mul_lt_mul_right]; all_goals linarith

      -- get strictAntiOn from y' < 0
      apply strictAntiOn_of_deriv_neg
      . exact convex_Ioi 1
      . apply continuousOn_of_forall_continuousAt
        intro x hx
        exact (hy' x hx).continuousAt
      intro x hx
      rw [interior_Ioi, mem_Ioi] at hx
      simp [(hy' x (by linarith)).deriv]
      exact hy'_pos x hx

    -- so we have y 2008 > y 2009
    have h2: y 2008 > y 2009 := by
      exact (h1.lt_iff_lt (show (1:ℝ) < 2009 by linarith) (show (1:ℝ) < 2008 by linarith)).mpr (by linarith)
    norm_num [y] at h2
    -- which means log(2009)/log(2008) > log(2010)/log(2009)
    exact h2
