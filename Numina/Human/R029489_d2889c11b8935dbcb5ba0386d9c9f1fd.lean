import Mathlib

open Real

/- $9 \cdot 13$ If $\left(\log _{2} 3\right)^{x}-\left(\log _{5} 3\right)^{x} \geqslant\left(\log _{2} 3\right)^{-y}-\left(\log _{5} 3\right)^{-y}$, then
(A) $x-y \geqslant 0$
(B) $x+y \geqslant 0$
(C) $x-y \leqslant 0$
(D) $x+y \leqslant 0$
(China High School Mathematics League, 1999) -/
theorem inequalities_98684 {x y : ℝ}
    (h : (logb 2 3)^x - (logb 5 3)^x ≥ (logb 2 3)^(-y) - (logb 5 3)^(-y)) :
    x + y ≥ 0 := by
  -- first prove facts about logb 2 3 and logb 5 3, in particular their relation to 0 and 1
  have : 0 < logb 5 3 := by
    rw [← Real.log_div_log]
    positivity
  have : 1 < logb 2 3 := by
    rw [show 1 = logb 2 2 by simp]
    gcongr <;> norm_num
  have : logb 5 3 < 1 := by
    rw [show 1 = logb 5 5 by simp]
    gcongr <;> norm_num
  -- now prove the derivative of a^x (since mathlib doesn't has this now it seems)
  have h_deriv {a x : ℝ} (h : 0 < a) : deriv (fun x : ℝ ↦ a^x) x = a ^ x * log a := by
    apply HasDerivAt.deriv
    apply HasStrictDerivAt.hasDerivAt
    apply Real.hasStrictDerivAt_const_rpow
    assumption
  -- also about it's differentiability at x
  have h_deriv' {a x : ℝ} (h : 0 < a) : DifferentiableAt ℝ (fun x : ℝ => a ^ x) x := by
    apply HasDerivAt.differentiableAt
    apply HasStrictDerivAt.hasDerivAt
    apply Real.hasStrictDerivAt_const_rpow
    assumption
  -- we'll prove a^x - b^x is strictly monotonous when b < 1, 1 < a, 0 < b
  have h_mono {a b : ℝ} (h : b < 1) (h' : 0 < b) (h'' : 1 < a) : StrictMono (fun x : ℝ ↦ a^x - b^x) := by
    apply strictMono_of_deriv_pos
    rintro x
    -- in derivative a^x * log a - b^x * logb, all terms are positive except log b, which cancels out the subtraction
    rw [deriv_sub, h_deriv, h_deriv]
    . apply add_pos
      . apply mul_pos
        . exact rpow_pos_of_pos (by linarith) x
        . exact log_pos (by assumption)
      . simp
        apply mul_neg_of_pos_of_neg
        . exact rpow_pos_of_pos (by linarith) x
        . exact log_neg (by assumption) (by assumption)
    . assumption
    . linarith
    . exact h_deriv' (by linarith)
    . exact h_deriv' (by assumption)
  -- since given equation is f(-y) ≤ f(x) for f (x) = (logb 2 3)^x - (logb 5 3)^x, we have -y ≤ x then it's obvious
  have : -y ≤ x := by
    replace h_mono := h_mono ‹logb 5 3 < 1› ‹0 < logb 5 3› ‹1 < logb 2 3›
    exact le_imp_le_of_lt_imp_lt h_mono.imp h
  linarith