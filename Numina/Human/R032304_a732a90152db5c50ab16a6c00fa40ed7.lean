import Mathlib

/- Find $x^2+y^2$ if $x$ and $y$ are positive integers such that
\begin{align*}
xy+x+y&=71, \\
x^2y+xy^2&=880.
\end{align*} -/
theorem algebra_95734 {x y : ℤ} (hx : x > 0) (hy : y > 0)
(h1 : x * y + x + y = 71) (h2 : x ^ 2 * y + x * y ^ 2 = 880) :
x ^ 2 + y ^ 2 = 146 := by
--We let $a$ and $b$ denote sum and product of $x$ and $y$, respectively.
  set a := x+y with ha
  set b := x*y with hb
--Substituting yields the equations $a+b=71$ and $ab=880$.
  rw [add_assoc, ← ha, add_comm] at h1
  have h2': a*b = 880 := by
    rw [← h2, ha, hb]
    ring_nf
--We use the fact that $a$ and $b$ are the roots of the quadratic equation $t^2-71t+880=0$, thus they are $16$ and $55$.
  have (t : ℤ) : (t-a)*(t-b)=(t^2 - 71*t + 880) := by
    calc (t-a)*(t-b) = t^2 - (a+b)*t + a*b := by ring
      _ = t^2 - 71*t + 880 := by rw [h1, h2']
  have prod (t : ℤ) : (t-a)*(t-b) = (t-16)*(t-55) := by
    rw [this]
    ring
  have : (a = 16 ∧ b = 55) ∨ (a = 55 ∧ b = 16) := by
    have ta := prod a
    simp only [sub_self, zero_mul, zero_eq_mul, sub_eq_zero] at ta
    omega
--We rewrite $x^2+y^2$ as $(x+y)^2-2xy=a^2-2b$.
  have hxy : x^2 + y^2 = (x+y)^2 - 2*(x*y) := by ring_nf
  rw [hxy, ← ha, ← hb]
--We substitute $a=16$ and $b=55$ ($a=55, b=16$ respectively) to obtain the result.
  rcases this with (h1655|h5516)
--If $a=16$ and $b=55$, we obtain $a^2-2b=146$.
  · rw [h1655.1, h1655.2]
    ring_nf
--If $a=55$ and $b=55$, we obtain a contradiction.
  · exfalso
    rw [ha, hb] at h5516
    have : x ≤ 16 ∧ y ≤ 16 := by
      constructor
      · apply Int.le_of_dvd; norm_num; use y; rw [← h5516.2]
      · apply Int.le_of_dvd; norm_num; use x; rw [mul_comm, ← h5516.2]
    linarith