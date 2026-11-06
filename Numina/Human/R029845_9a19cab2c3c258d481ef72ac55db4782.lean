import Mathlib

/- 5. Let $a, b$, and $c$ be positive real numbers, $a, b, c \neq 1$. If


$$

\log _{a} 2018+\log _{c} 2018=2 \log _{b} 2018

$$


prove:
a) $\log _{a} 2019+\log _{c} 2019=2 \log _{b} 2019$;
b) $a^{2}=(a c)^{\log _{c} b}$.
 -/
theorem algebra_106327 (a b c : ℝ) (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1) (hc : 0 < c ∧ c ≠ 1)
    (h : Real.logb a 2018 + Real.logb c 2018 = 2 * Real.logb b 2018) :
    Real.logb a 2019 + Real.logb c 2019 = 2 * Real.logb b 2019 ∧ a^2 = (a * c)^(Real.logb c b) := by
  -- prove non-zero facts for division
  have : Real.log 2018 ≠ 0 := by refine Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have : Real.log a ≠ 0 := by refine Real.log_ne_zero_of_pos_of_ne_one ha.left ha.right
  have : Real.log b ≠ 0 := by refine Real.log_ne_zero_of_pos_of_ne_one hb.left hb.right
  have : Real.log c ≠ 0 := by refine Real.log_ne_zero_of_pos_of_ne_one hc.left hc.right
  and_intros
    -- to prove first goal multiply by log 2019/log 2018, and we're done
  . repeat rw [← Real.log_div_log] at h ⊢
    replace h := congrArg (· * Real.log 2019 / Real.log 2018) h
    ring_nf at h ⊢
    convert h using 2
    all_goals field_simp; try ring
    -- to prove second fact, multiply out everything and cancel log 2018
  . repeat rw [← Real.log_div_log] at h
    field_simp at h
    replace h : (Real.log b * Real.log c + Real.log b * Real.log a) * Real.log 2018 = 2 * Real.log a * Real.log c * Real.log 2018 := by linear_combination h
    simp [‹Real.log 2018 ≠ 0›] at h
    -- divide by log c
    replace h := congrArg (· / Real.log c) h
    replace h : Real.log b * Real.log c / Real.log c + Real.log b / Real.log c * Real.log a = 2 * Real.log a * (Real.log c / Real.log c) := by linear_combination h
    simp [‹Real.log c ≠ 0›] at h
    -- now do some algebraic manipulation to get log of target equation
    nth_rw 1 [← @Real.rpow_logb c b hc.left hc.right hb.left] at h
    rw [Real.log_div_log, ← Real.log_rpow (ha.left), ← Real.log_rpow (ha.left), ← Real.log_mul, ← Real.mul_rpow (by linarith) (by linarith), show a^(2:ℝ) = a^2 by norm_cast] at h
    -- use injectivity of log to prove target
    . rw [eq_comm, mul_comm]
      refine Real.log_injOn_pos ?_ ?_ h
      . simp
        have := ha.left
        have := hc.left
        positivity
      . simp
        have := ha.left
        positivity
    -- during algebraic manipulation, we needed c ^ Real.logb c b ≠ 0
    . by_contra h
      have := Real.rpow_eq_zero (by linarith) (by rw [← Real.log_div_log]; positivity) |>.mp h
      linarith
    -- during algebraic manipulation, we needed a ^ Real.logb c b ≠ 0
    . by_contra h
      have := Real.rpow_eq_zero (by linarith) (by rw [← Real.log_div_log]; positivity) |>.mp h
      linarith


#check Real.log_injOn_pos

#check Real.rpow_natCast