import Mathlib

open Topology Filter Real TopologicalSpace Finset
open scoped BigOperators

/- 25.18. a) Prove that $\lim _{n \rightarrow \infty} \frac{n^{k}}{a^{n}}=0$ for any natural $k$ and any $a>1$.

b) Prove that $\lim _{n \rightarrow \infty} \frac{\left(\log _{a} n\right)^{k}}{n}=0$ for any natural $k$ and any $a>1$. -/
theorem calculus_228185 (a : ℝ) (ha : a > 1) (k : ℕ) :
    Tendsto (λ n => n ^ k / a ^ n) atTop (𝓝 0) ∧ Tendsto (λ n => (logb a n) ^ k / n) atTop (𝓝 0) := by
  and_intros
  -- first goal, we'll show n^k = o(a^n) and that both are simultaneously 0 eventually
  . refine Asymptotics.isLittleO_iff_tendsto' ?_ |>.mp ?_
    -- as a^x is never 0 (if x is 0, then it's 1, if x ≠ 0 then rpow_eq_zero provides proof), the two functions are eventually simultaneously 0 vacuously
    . have (x : ℝ) : a ^ x ≠ 0 := by
        by_cases h : x = 0
        . rw [h]
          simp
        . simp
          rw [rpow_eq_zero (by linarith) h]
          linarith
      simp_rw [this]
      simp
    -- to prove little o equation, wright rhs as exp(log a * n)
    . convert_to (fun n => n ^ k) =o[atTop] (fun n => exp (log a * n))
      . ext x
        refine rpow_def_of_pos (by linarith) x
      -- as log a > 0, this is true from isLittleO_pow_exp_pos_mul_atTop
      apply isLittleO_pow_exp_pos_mul_atTop
      exact log_pos ha
  -- second goal, we'll show log_a(n)^k = o(n) and that both are simultaneously 0 eventually
  . refine Asymptotics.isLittleO_iff_tendsto' ?_ |>.mp ?_
    -- x ≠ 0 implies x = 0 → log_a(x)^k = 0 vacuously, so proving eventually x ≠ 0 is enough
    . have (x : ℝ) (h : x ≠ 0) (h' : x = 0) : logb a x ^ k = 0 := by tauto
      refine Eventually.mono ?_ this
      -- i.e. we have to prove there is a bound above which x ≠ 0, simply use 1 as that bound
      simp
      use 1
      rintro x hx
      linarith
    -- write logb as division and take out (1 / log (a^k)), this is an unit as log (a^k) is not 0
    . simp_rw [logb, div_pow]
      convert_to (fun n => (1 / log a ^ k) * log n ^ k) =o[atTop] id
      . ext x
        ring
      have : IsUnit (1 / log a ^ k) := by
        simp [show a ≠ 0 by linarith, show a ≠ 1 by linarith, show a ≠ -1 by linarith]
      -- so we can change gaol to be just (log n)^k = o(n)
      rw [Asymptotics.isLittleO_const_mul_left_iff' this]
      -- which is true by isLittleO_pow_log_id_atTop
      apply isLittleO_pow_log_id_atTop