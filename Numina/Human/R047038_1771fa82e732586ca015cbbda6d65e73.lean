import Mathlib

/-
50. (SWE 3) The function $\varphi(x, y, z)$, defined for all triples 
$(x, y, z)$ of real numbers, is such that there are two functions $f$ and
$g$ defined for all pairs of real numbers such that  
$$ \varphi(x, y, z)=f(x+y, z)=g(x, y+z) $$ 
for all real $x, y$, and $z$. Show that there is a 
function $h$ of one real variable such that  $$ \varphi(x, y, z)=h(x+y+z) $$  
for all real $x, y$, and $z$.

50. Since $\varphi(x, y, z)=f(x+y, z)=\varphi(0, x+y, z)=g(0, x+y+z)$, 
it is enough to put $h(t)=g(0, t)$.
-/

theorem phifun (p : ℝ → ℝ → ℝ → ℝ) (f g : ℝ → ℝ → ℝ) 
(prop1 : ∀ x y z, p x y z = f (x + y) z)
(prop2 : ∀ x y z, p x y z = g x (y + z)) :
∃ h : ℝ → ℝ, ∀ x y z, p x y z = h (x + y + z) := by
  have obvlem : ∀ x y z, g x (y + z) = f (x + y) z := by
    intros x y z
    rw [← prop1, prop2]
  use g 0
  intros x y z
  rw [obvlem, prop1]
  simp only [implies_true, zero_add]