import Mathlib
open Real


/-
If $a$ and $b$ are positive real numbers such that $a \cdot 2^{b}=8$ and $a^{b}=2$, compute $a^{\log _{2} a} 2^{b^{2}}$.
-/
theorem algebra_610580 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h0: a* 2^b = 8) (h1: a^b = 2) : a^((log a)/ log 2) * 2^(b^2) = 128 := by

  -- Take logarithm to the 2 of both sides at the equation to prove.
  have hend: log (a^((log a)/ log 2) * 2^(b^2)) = (log a /log 2)* log a + b^2 * log 2 := by

    -- Some positivity which make the 2 logarithm below be meaningful.
    have _1 : a^((log a)/ log 2) > 0 := by positivity
    have _2 : (2:ℝ)^(b^2) > 0 := by positivity
    calc
      _ = log (a^((log a)/ log 2)) + log (2^(b^2)) := by
        rw [log_mul]; linarith; norm_cast at _2; linarith
      _ = ((log a)/ log 2) * log a + log (2^(b^2)) := by
        rw [log_rpow]; linarith
      _ = ((log a)/ log 2) * log a + b^2 * log 2 := by rw [log_rpow]; linarith

  -- Take logarithm to h0
  have h2: log a + b* log 2 = 3*log 2 := by
    calc
      _ = log (a* 2^b) := by
        rw [log_mul]; rw [log_rpow]
        norm_num; linarith;
        have : 1 ≤ (2:ℝ)^b := by
          have _1 : 0 ≤ b := by linarith
          have _2 : 1 ≤ 2 := by norm_num
          apply one_le_rpow _ _
          linarith; linarith
        linarith
      _ = log (8:ℝ) := by rw [h0.symm]
      _ = log (2^3) := by norm_num
      _ = 3*log 2 := by rw [log_pow]; norm_cast
  
  -- Take logarithm to h1
  have h3: b * (log a) = log 2 := by
    calc
      _ = log (a^b) := by
        rw [log_rpow]
        linarith
      _ = log (2:ℝ) := by rw [h1.symm]

  -- Change the variavle to simlified expression.
  let u:ℝ := log a

  -- Basic  arithmetic on log and pow of 2
  have _1: u + b* log 2 = 3*log 2 := by unfold u; linarith

  -- rw the u = log a back in order to use h3.
  have _2 : u*b =  log 2 := by unfold u; linarith
  have _3: log (a ^ (log a / log 2) * 2 ^ b ^ 2) = u / log 2 * u + b ^ 2 * log 2 := by unfold u; linarith

  -- We have 2ab = (a+b)^2 - a^2- b^2, and we know a+b and a^2 + b^2
  have _3' : u / log 2 * u + b ^ 2 * log 2 = 7*log 2 := by
    calc
      _ = (u^2 + (b*log 2)^2)/log 2 := by
        have : log 2 > 0 := by linarith [log_two_gt_d9]
        field_simp; ring_nf
      _ = ((u + b*log 2)^2 - 2 * (u * b) * log 2)/log 2 := by ring_nf
      _ = ((3*log 2)^2 - 2*log 2 * log 2)/log 2 := by rw [_1,_2]
      _ = _ := by field_simp; ring_nf
  
  -- Calculation the result.
  calc
    _ = exp  (log (a ^ (log a / log 2) * 2 ^ b ^ 2)) := by  rw [exp_log]; positivity
    _ = exp (7*log 2) := by rw [_3, _3']
    _ = (exp (log (2^7))) := by
      rw [←log_rpow]; norm_cast; norm_num
    _ = 2^7 := by rw [exp_log]; norm_cast
    _ = 128 := by norm_num