import Mathlib
open Real

/-
Suppose $x, y$, and $z$ are real numbers greater than 1 such that

$$
\begin{aligned}
& x^{\log _{y} z}=2 \\
& y^{\log _{z} x}=4, \text { and } \\
& z^{\log _{x} y}=8
\end{aligned}
$$

Compute $\log _{x} y$.
-/
theorem algebra_610648 {x y z : ℝ} (hx : 1 < x) (hy : 1 < y) (hz : 1 < z) (h1: x ^ (logb y z) = 2) (h2: y ^ (logb z x) = 4) (h3: z ^ (logb x y) = 8) : (logb x y = sqrt 3) := by

  have hxp: log x > 0 := by
       apply log_pos; exact hx
  have hyp: log y > 0 := by
       apply log_pos; exact hy
  have hzp: log z > 0 := by
       apply log_pos; exact hz
  
  -- take logarithm at both sides of h1, h2, h3 respectively

  have : log (x ^ (logb y z)) = (logb y z) * log x := by
    rw [log_rpow]; linarith
  have h1': log (x ^ (logb y z)) = (log z / log y) * log x := by rw [log_div_log]; exact this
  rw [h1] at h1'

  have : log (y ^ (logb z x)) = (logb z x) * log y := by
    rw [log_rpow]; linarith
  have h2': log (y ^ (logb z x)) = (log x / log z) * log y := by rw [log_div_log]; exact this
  rw [h2] at h2'

  have : log (z ^ (logb x y)) = (logb x y) * log z := by
    rw [log_rpow]; linarith
  have h3': log (z ^ (logb x y)) = (log y / log x) * log z := by rw [log_div_log]; exact this
  rw [h3] at h3'

  -- mul h2' and h3'
  have h23: log 4 * log 8 = (log y)^2 := by
    rw [h2', h3']
    field_simp; ring_nf
  
  -- mul h1' and h2'
  have h12: log 2 * log 4 = (log x)^2 := by
    rw [h1', h2']
    field_simp; ring_nf
  
  -- dive h23 by h12

  have h2312: log 4 * log 8 / (log 2 * log 4) = (log y / log x) ^ 2 := by
    rw [h23, h12]; field_simp
  
  have _1 : log 4 > 0 := by
    apply log_pos; linarith
  have _2 : log 2 > 0 := by
    apply log_pos; linarith
  have _3 : log 8 = 3 * log 2 := by
    rw [show (8:ℝ) = 2 ^ 3 by norm_num]
    rw [log_pow]; simp
  rw [_3] at h2312
  calc
    _ = log y / log x := by rw [log_div_log]
    _ = sqrt ((log y / log x)^2) := by
      have : log y / log x ≥ 0 := by positivity
      rw [sqrt_sq this]
    _ = sqrt 3 := by
      rw [h2312.symm]
      have : log 4 * (3 * log 2) / (log 2 * log 4) = 3 := by field_simp; ring_nf
      rw [this]
    




    