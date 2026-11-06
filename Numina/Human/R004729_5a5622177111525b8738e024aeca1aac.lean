import Mathlib

/-Given three distinct integers x,y,z whose sum lies between 40 and 44. 
If x,y,z form an arithmetic sequence with a common difference of d, and 
x+y,y+z,z+x form a geometric sequence with a common ratio of q, then dq= 42 
-/
theorem algebra_311949 (x y z d q : ℤ) (h₀ : x ≠ y) 
    (h₃ : 40 < x + y + z) (h₄ : x + y + z < 44) (h₅ : y - x = d) (h₆ : z - y = d)
    (h₇ : (x + y) * q = y + z) (h₈ : (y + z) * q = z + x) :
    d * q = 42 := by
  have hy : y = x + d := by linarith
  have hz : z = x + 2 * d := by linarith [h₅, h₆]
  have h9 : (x + y) * q = y + z := h₇
  rw [hy, hz] at h9
  have h10 : (y + z) * q = z + x := h₈
  rw [hy, hz] at h10
  -- we write the equations in terms of x and d and q--
  have eq1 : (2 * x + d) * q = 2 * x + 3 * d := by linarith
  have eq2 : (2 * x + 3 * d) * q = 2 * x + 2 * d := by linarith
  -- then we try to find q first, so we can get x and d- -
  have h11 : d ≠ 0 := by
    by_contra h
    have h12 : x = y := by linarith [h₅, h]
    contradiction
  have h12 : 2 * q + 1 = 0 := by 
    have eq3 : (2 * x + 3 * d) * q - (2 * x + d) * q = (2 * x + 2 * d) - (2 * x + 3 * d) := by linarith [eq1, eq2]
   -- from here we can derive q --
    have eq4 : 2 * d * q = -d := by nlinarith [eq3]
    have h13 : d ≠ 0 := h11
    have : 2 * q + 1 = 0 := by
      apply (mul_left_inj' h13).mp
      linarith
    linarith
  -- then we get a simplifed form of relation between x and d --
  have h13 : 6 * x + 7 * d = 0 := by 
    nlinarith [eq1, h12, h11]
  have h14 : x + y + z = 3 * x + 3 * d := by
    rw [hy, hz]
    ring
  -- then we compute x and d by inequality --
  have h15 : 40 < 3 * x + 3 * d := by linarith [h₃, h14]
  have h16 : 3 * x + 3 * d < 44 := by linarith [h₄, h14]
  have h17 : x + d = 14 := by 
    omega
  have hd : d = -84 := by 
    omega
  -- finally, plug them into the equation to get the result --
  have hq2 : 2 * q = -1 := by linarith
  have h18 : d * q = 42 := by
    have hq2' : 2 * q = -1 := hq2
    have hd' : d = -84 := hd
    nlinarith
  exact h18
  