import Mathlib


/-
Let $a, b$, and $c$ be real numbers such that

$$
\begin{aligned}
a+b+c & =100 \\
a b+b c+c a & =20, \text { and } \\
(a+b)(a+c) & =24
\end{aligned}
$$

Compute all possible values of $b c$.
-/
theorem algebra_610726 (a b c : ℝ) (h1: a+b+c = 100) (h2: a*b + b*c  + c*a = 20) (h3: (a+b)*(a+c) = 24): (b*c = -176)∨(b*c = 224) := by
  
  -- Expand h3: a^2 + ac + ab + bc = 24 using distributive property
  have h3': a^2 + a*b + b*c  + c*a = 24 := by
    calc
      _ = (a+b)*(a+c) := by ring_nf
      _ = _ := by exact h3

  -- Sub h3' by h2 thus a^2 = 4
  have ha: a^2 = 4 := by
    calc
      _ = a^2 + a*b + b*c  + c*a - (a*b + b*c  + c*a) := by ring_nf
      _ = _ := by
        rw [h3', h2]; ring_nf
  
  -- Sub h1^2 by h2 and h3 thus b^2 + c^2 is 100^2 - 44
  have hbcsq : b^2 + c^2 = 100^2 - 44 := by
    calc
      _ = a^2 + b^2 + c^2 + 2*(a*b + b*c  + c*a) - (a*b + b*c  + c*a) - (a+b)*(a+c) := by ring_nf
      _ = (a+b+c)^2 - (a*b + b*c  + c*a) - (a+b)*(a+c) := by ring_nf
      _ = 100^2 - 20 - 24 := by rw [h1, h2, h3]
      _ = _ := by norm_num

  -- Solve the a^2 = 4 on real number
  have  ha': a= 2 ∨ a=-2 := by
    have : (a+2)*(a-2) = 0 := by
      ring_nf; rw [ha]; norm_num
    simp at this
    rcases this with hl | hr
    have : a = -2 := by linarith
    tauto
    have : a = 2 := by linarith
    tauto
  
  rcases ha' with hu|hv
  
  -- If a = 2
  have : b+c = 98 := by linarith
  have hbc: b*c = -176 := by
    calc
      _ = ((b+c)^2 - (b^2 + c^2))/2 := by ring_nf
      _ = (98^2 - (100^2 - 44))/2 := by rw[this,hbcsq]
      _ = _ := by norm_num
  tauto
  -- If a = -2
  have : b+c = 102 := by linarith
  have hbc: b*c = 224 := by
    calc
      _ = ((b+c)^2 - (b^2 + c^2))/2 := by ring_nf
      _ = (102^2 - (100^2 - 44))/2 := by rw[this,hbcsq]
      _ = _ := by norm_num
  tauto