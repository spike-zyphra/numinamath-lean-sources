import Mathlib
open Real

/- Let's determine the geometric mean of the following two expressions:

$$
\frac{2\left(a^{2}-a b\right)}{35 b}, \quad \frac{10 a}{7\left(a b-b^{2}\right)}
$$ -/
theorem algebra_291411 {a b : ℝ} (ha : a > 0) (hb : b > 0) (hab: a ≠ b) :
    sqrt ((2 * (a ^ 2 - a * b) / (35 * b)) * (10 * a / (7 * (a * b - b ^ 2)))) = 2*a / (7 * b) := by

    have hab' : a - b ≠ 0 := by
      intro h
      have : a = b := by linarith
      tauto
    calc
      _ = sqrt ((2 * a * (a - b) / (35 * b)) * (10 * a / (7 * (a - b) * b))) := by ring_nf
      _ = sqrt ((2 * a  / (35 * b)) * (a - b) * (10 * a / (7 * (a - b) * b))) := by ring_nf
      _ = sqrt ((2 * a  / (35 * b)) * (a - b) * ((10 * a / ((7 * b) * (a - b))))) := by ring_nf
      _ = sqrt ((2 * a  / (35 * b)) * (a - b) * ((10 * a / (7 * b)) * 1/(a - b) )) := by field_simp
      _ = sqrt ((2 * a  / (35 * b)) * (a - b) * (10 * a / (7 * b)) * 1/(a - b) ) := by ring_nf
      _ = sqrt ((2 * a  / (35 * b)) * (10 * a / (7 * b)) *   ((a - b)/(a - b)) ) := by ring_nf
      _ = sqrt ((2 * a  / (35 * b)) * (10 * a / (7 * b)) * 1) := by rw [show (a-b)/(a-b) = 1 by field_simp]
      _ = sqrt (2 * a  * (1/(35 * b)) * (10 * a) * (1/(7 * b))) := by ring_nf
      _ = sqrt (2 * a  * (10 * a) * (1/(35 * b) * (1/(7 * b)))) := by ring_nf
      _ = sqrt (20 * a^2 * (1/(35 * b) * (1/(7 * b)))) := by ring_nf
      _ = sqrt (20 * a^2 * (1/(245*b^2))) := by
        field_simp
        have _1: b = sqrt b * sqrt b := by
          ring_nf; rw [sq_sqrt (by positivity)]
        have _2: sqrt 245 = sqrt 35 * sqrt 7 := by
          have : (245:ℝ) = 35 * 7 := by norm_num
          rw [this, sqrt_mul]
          linarith
        rw [_2]
        calc
          _ = sqrt 35 * sqrt 7 * sqrt b * sqrt b := by
            nth_rewrite 1 [_1]
            linarith
          _ = _ := by linarith
      _ = sqrt ((20/245)*(a/b)^2) := by field_simp
      _ = sqrt ((2/7)^2*(a/b)^2) := by norm_num
      _ = sqrt ((2*a/(7*b))^2) := by field_simp
      _ = 2 * a / (7 * b) := by
        have : 2*a/(7*b) > 0 := by positivity
        rw [sqrt_sq]; linarith
      


          



        
