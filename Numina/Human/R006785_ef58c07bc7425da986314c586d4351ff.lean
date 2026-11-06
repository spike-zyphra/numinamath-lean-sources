import Mathlib

set_option linter.unusedVariables false

lemma lemma_1 (a b: ℕ): a = a / b * b + a % b := by
  suffices b * (a / b) + a % b = a by
    nlinarith
  apply Nat.div_add_mod

/-Let  b  be an integer greater than 1 . Let  d_{2}, d_{1}, d_{0}, c  be non-negative integers such that  d_{i}<b  for  i \in\{0,1,2\}  and  c<b . Let  X  be the number whose base-  b  representation is  \left(d_{2} d_{1} d_{0}\right)_{b} , which means  X=d_{2} b^{2}+d_{1} b+d_{0} . Let  Y  be the number whose base-  b  representation is  (c)_{b} , which means  Y=c .
Define the following sequence of integers:  p_{0}=c \cdot d_{0} r_{0}=p_{0} \bmod b q_{0}=\left\lfloor p_{0} / b\right\rfloor 
\begin{array}{l}
p_{1}=c \cdot d_{1}+q_{0} r_{1}=p_{1} \bmod b q_{1}=\left\lfloor p_{1} / b\right\rfloor \\
p_{2}=c \cdot d_{2}+q_{1} r_{2}=p_{2} \bmod b q_{2}=\left\lfloor p_{2} / b\right\rfloor
\end{array}
Let  r_{3}=q_{2} .
Show that the product  X \cdot Y  is the number whose base-  b  representation is  \left(r_{3} r_{2} r_{1} r_{0}\right)_{b} . This means  X \cdot Y=r_{3} b^{3}+r_{2} b^{2}+   r_{1} b+r_{0} -/

theorem number_theory_641131 (b d0 d1 d2 X Y c p0 p1 p2 q0 q1 q2 r0 r1 r2 r3 d0 d1 d2: ℕ)
(h1: 1 < b) (h2: d0 < b) (h3: d1 < b) (h4: d2 < b) (h5: c < b) (h6: X = d2 * b^2 + d1 * b + d0) (h7: Y = c)
(h8: p0 = c * d0) (h9: r0 = p0 % b) (h10: q0 = p0 / b) (h11: p1 = c * d1 + q0) (h12: r1 = p1 % b)
(h13: q1 = p1 / b) (h14: p2 = c * d2 + q1) (h15: r2 = p2 % b) (h16: q2 = p2 / b) (h17: r3 = q2):
X * Y = r3 * b^3 + r2 * b^2 + r1 * b + r0 := by

  simp [h6, h7]
  ring_nf
  have f1: d0 * c = q0 * b + r0 := by
    clear *- h10 h9 h8 h1
    rw [show d0 * c = p0 by nlinarith]
    clear h8
    simp [h9, h10]
    exact lemma_1 p0 b
  rw [f1]
  clear f1
  rw [show d2 * b ^ 2 * c + b * d1 * c + (q0 * b + r0) = d2 * b ^ 2 * c + b * (c * d1 + q0) + r0 by ring]
  have f2: c * d1 + q0 = q1 * b + r1 := by
    rw [← h11]
    simp [h13, h12]
    exact lemma_1 p1 b
  rw [f2]
  clear f2
  rw [show d2 * b ^ 2 * c + b * (q1 * b + r1) + r0 = (c * d2 + q1) * b ^ 2 + r1 * b + r0 by ring]
  have f3: c * d2 + q1 = q2 * b + r2 := by
    rw [← h14]
    simp [h15, h16]
    exact lemma_1 p2 b
  rw [f3]
  clear f3
  ring_nf
  simp [h17]
  ring

