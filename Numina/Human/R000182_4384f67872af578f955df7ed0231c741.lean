import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Let  $a$  be a fixed integer. Find all integer solutions  $x, y, z$  of the system
\[5x + (a + 2)y + (a + 2)z = a,\]
\[(2a + 4)x + (a^2 + 3)y + (2a + 2)z = 3a - 1,\]
\[(2a + 4)x + (2a + 2)y + (a^2 + 3)z = a + 1.\]-/
theorem number_theory_8504 (a x y z : ℤ) :
    5 * x + (a + 2) * y + (a + 2) * z = a ∧
    (2 * a + 4) * x + (a^2 + 3) * y + (2 * a + 2) * z = 3 * a - 1 ∧
    (2 * a + 4) * x + (2 * a + 2) * y + (a^2 + 3) * z = a + 1 ↔
    (a = 1 ∧ x = -1 ∧ z = 2 - y) ∨
    (a = -1 ∧ x = 0 ∧ y = -1 ∧ z = 0) ∨
    (a = 0 ∧ x = 0 ∧ y = -1 ∧ z = 1) ∨
    (a = 2 ∧ x = -6 ∧ y = 5 ∧ z = 3) := by
  constructor
  swap
  -- Verify if a = 1 then (-1,y,2-y) is solution
  -- Verify if a = -1 then (0,-1,0) is solution
  -- Verify if a = 0 then (0,-1,1) is solution
  -- Verify if a = 2 then (-6,5,3) is solution
  . rintro (h | h | h | h)
    any_goals simp [h.1, h.2.1, h.2.2]
    ring_nf; trivial
  rintro ⟨h1, h2, h3⟩
  -- Subtracting the third equation from the second, we get $(a-1)^2(y-z)=2(a-1)\quad(*)$
  have h : (y - z) * (a - 1) * (a - 1) = 2 * (a - 1) := by linear_combination h2 - h3
  by_cases ha1 : a = 1
  --**Case 1.**  $a=1$ Then the system becomes
  --\begin{eqnarray*}5x+3(y+z) &=& 1 6x+4(y+z) &=&2\end{eqnarray*}
  --thus  $a=1\implies (x,y,z)=(-1,n,2-n),n\in\mathbb{Z}$
  . simp [ha1] at h1 h2
    left
    exact ⟨ha1, by omega, by omega⟩
  -- **Case 2.**  $a\neq 1$ Then  $(*)$  yields  $y-z={2\over a-1}$ .
  -- Since  $y-z$  is integer, we get  $a-1\in\{\pm 1,\pm 2\}\iff a\in\{-1,0,2,3\}$ .
  replace ha1 : a  - 1 ≠ 0 := by omega
  apply_fun (· / (a - 1)) at h
  field_simp at h
  have ha1_dvd : a - 1 ∣ 2 := by use y - z; linear_combination -h
  rw [← abs_dvd] at ha1_dvd
  have := Int.le_of_dvd (by norm_num) ha1_dvd
  rw [abs_le] at this
  have : -1 ≤ a := by omega
  have : a ≤ 3 := by omega
  interval_cases a
  -- Solving the system in each of those cases we get the following:
  -- a)  $a=-1\implies (x,y,z)=(0,-1,0)$ b)  $a=0\implies (x,y,z)=(0,-1,1)$
  -- c)  $a=2\implies (x,y,z)=(-6,5,3)$
  -- For  $a=3$  the system reduces to a single equation  $x+y+z={3\over 5}$
  -- which obviously has no integer solutions.
  any_goals simp_all; omega
  norm_num at ha1
