import Mathlib

/- Find an ordered pair $(x,y)$ that solves the system: \begin{align*} 2x - 3y &= -3.2 - 0.2x + 0.1y,\\ x &= 0.6x - y + 8.8 \end{align*} -/
theorem algebra_20572 {x y : ℝ} (h1 : 2*x-3*y=-3.2-0.2*x+0.1*y) (h2 : x=0.6*x-y+8.8) :
    (x,y)=(7,6) := by 
  norm_num at h1 h2 ⊢
  apply And.intro
  next => linarith
  next => linarith