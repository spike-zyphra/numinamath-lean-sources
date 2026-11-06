import Mathlib

/-- Let $\(a, b, c\)$ be non-zero real numbers and $\(a \neq b\)$. Prove that if the equations $\(x^2 + ax + bc = 0\)$ and $\(x^2 + bx + ca = 0\)$ have a common root, then the remaining roots satisfy the equation $\(x^2 + cx + ab = 0\)$.-/
theorem algebra_4033
  (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (h_ne : a ≠ b)
  (x₁ x₂ x₃ : ℝ)
  -- Let $x_1,x_2$ are roots of $ x^2+a*x+b*c$ 
  (heq1 : ∀(x:ℝ),(x-x₁)*(x-x₂)=x^2+a*x+b*c)
  -- Let $x_2,x_3$ are roots of $x^2+b*x+a*c$
  (heq2 :  ∀(x:ℝ),(x-x₃)*(x-x₂)=x^2+b*x+a*c)
  :∀(x:ℝ),(x-x₃)*(x-x₁)=x^2+c*x+b*a := by
  intro x
  -- replace $x$ by 0 in `heq1` and simplify
  have h10:= heq1 0
  ring_nf at h10
  -- replace $x$ by 0 in `heq2` and simplify
  have h20:= heq2 0
  ring_nf at h20
  have hm10:= heq1 (-1)
  -- replace $x$ by $x_2$ in `heq1` and simplify
  have hcom1:= heq1 x₂
  simp at hcom1
  -- replace $x$ by $x_2$ in `heq2` and simplify
  have hcom2:= heq2 x₂
  simp at hcom2
  rw[hcom1] at hcom2
  have hcom:(a-b) * x₂  =(a-b)*c:= by linarith
  have hx22:x₂= c:= by field_simp at hcom;cases hcom;assumption;by_contra;apply h_ne;linarith
  by_cases hz:x₂=0
  simp_all
  -- according to above equation, we have $x_1 = b*c/x_2$
  have hx1:x₁ = b*c/x₂:= by field_simp;exact h10
  -- according to above equation, we have $x_3 = a*c/x_2$
  have hx3:x₃ = a*c/x₂:= by field_simp;exact h20
  rw [hx22] at hx1
  rw [hx22] at hx3
  field_simp at hx1
  field_simp at hx3
  rw[hx1,hx3]
  rw[hx22] at hcom1
  have hcc:(a+b+c)=0/c:= by field_simp;linarith
  simp at hcc
  have hc:c=-b-a:= by linarith
  rw[hc]
  ring
