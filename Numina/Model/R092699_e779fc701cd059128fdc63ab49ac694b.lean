import Mathlib

/- Given that $m$ is an integer and $-60 < m < -30$, the system of linear equations in two variables $x$ and $y$ $\begin{cases}2x-3y=5 \\ -3x-7y=m \end{cases}$ has integer solutions, then $m=$ ___          ___ , ${x}^2+y=$ ___          ___. -/
theorem algebra_2255 {m : ℤ} {x y : ℤ} (h : -60 < m ∧ m < -30) (h1 : 2*x-3*y=5) (h2 : -3*x-7*y=m) :
    m=-42 ∧ x^2+y=52 := by
  have h3 : -60 < m := h.1
  have h4 : m < -30 := h.2
  
  have : m = -42 := by 
    omega
  
  have hm : m = -42 := by 
    omega
  
  have hx : x = 7 := by 
    rw [hm] at h2
    omega
  
  have hy : y = 3 := by 
    rw [hm] at h2
    omega
  
  constructor
  · exact hm
  · -- Show that x^2 + y = 52
    have : x ^ 2 + y = 52 := by 
      rw [hx, hy]
      norm_num
    exact this