import Mathlib

open Filter Real Topology

/- 7. If $n \in \mathbf{N}^{*}$, then $\lim _{n \rightarrow \infty} \sin ^{2}\left(\pi \sqrt{n^{2}+n}\right)=$ $\qquad$ (Contributed by Jian Weifeng) -/
theorem calculus_131543 :
    Tendsto (λ n : ℕ => (sin (π * sqrt (n^2 + n)))^2) atTop (𝓝 1) := by
  -- show that sin (π * sqrt (n^2 + n)))^2 = sin (π / (sqrt (1 + 1 / n) + 1))^2 for n > 0
  have eq (n : ℕ) (hn : n > 0) : sin (π * sqrt (n ^ 2 + n))^2 = sin (π / (sqrt (1 + 1 / n) + 1))^2 := calc
    -- we have sin (π * a) ^ 2 = sin (π * a - π * n) ^ 2 for any real a
    -- because sin (π * a - π * n) = (-1)^n * sin (π * a)
    sin (π * sqrt (n ^ 2 + n)) ^ 2 = sin (π * sqrt (n ^ 2 + n) - π * n) ^ 2 := by
        set a := π * _
        rw [show a - π * n = a + (-n : ℤ) * π by simp; ring]
        rw [sin_add_int_mul_pi, mul_pow]
        rw [← inv_zpow']
        norm_num
        rw [← pow_mul, mul_comm n 2, pow_mul]
        norm_num
    -- show that π * sqrt (n^2 + n) - π * n = π / (sqrt (1 + 1 / n) + 1)
    _ = sin (π / (sqrt (1 + 1 / n) + 1)) ^ 2 := by
        congr
        field_simp
        -- simplify the goal and get the following equality which needs to be proved
        -- π * (√(n ^ 2 + n) - n) * (√(n + 1) + √n) = π * √n
        rw [← mul_sub]
        -- we have √(n ^ 2 + n) - n = √n * (√(n + 1) - √n)
        have eq1 : √((n : ℝ) ^ 2 + n) - n = √n * (√(n + 1) - √n) := by
          rw [mul_sub, mul_self_sqrt (by positivity), ← sqrt_mul (by positivity)]
          ring_nf
        -- so the goal simplifies to π * √n * ((√(n + 1) + √n) * (√(n + 1) - √n))
        --                         = π * √n * ((n + 1 - n) = π * √n
        simp_rw [eq1, mul_assoc, mul_comm (_ - _), ←sq_sub_sq]
        repeat rw [sq_sqrt (by positivity)]
        ring
  -- we have that sin (π * sqrt (n^2 + n)))^2 is eventually equal to
  -- (fun x => sin (π * x) ^ 2) ∘ (fun n : ℕ => 1 / (sqrt (1 + 1 / n) + 1))
  have eq' : ((fun x => sin (π * x) ^ 2) ∘ (fun n : ℕ => 1 / (sqrt (1 + 1 / n) + 1))) =ᶠ[atTop] (fun n : ℕ => (sin (π * sqrt (n ^ 2 + n)))^2) := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    use 1
    intro n hn
    simp only [one_div, Function.comp_apply, eq n (by omega)]
    congr
  -- find the limit of (fun x => sin (π * x) ^ 2) ∘ (fun n : ℕ => 1 / (sqrt (1 + 1 / n) + 1))
  -- as n tends to infinity
  apply Filter.Tendsto.congr' eq'
  apply Filter.Tendsto.comp (y := 𝓝 (1 / 2))
  -- the limit of sin (π * x) ^ 2 as x tends to 1 / 2 is 1
  · nth_rw 2 [show 1 = sin (π * (1 / 2))^2 by norm_num [mul_div]]
    -- sin (π * x) ^ 2 is continuous so its limit at 1 / 2 is sin (π / 2)^2 = 1
    apply Continuous.tendsto
    fun_prop
  -- it is left to show that the limit of 1 / (sqrt (1 + 1 / n) + 1) is 1 / 2
  -- as n tends to infinity
  · apply Tendsto.div tendsto_const_nhds _ (by norm_num)
    rw [show (2 : ℝ) = √(1 + 0) + 1 by norm_num]
    -- the result follows from basic properties of the limit operation
    apply Tendsto.add_const
    apply Tendsto.sqrt
    apply Tendsto.const_add
    exact tendsto_one_div_atTop_nhds_zero_nat