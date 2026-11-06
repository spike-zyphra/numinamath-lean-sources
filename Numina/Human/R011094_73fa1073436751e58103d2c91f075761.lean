import Mathlib
open Real

/-
If $a, b$ are nonzero real numbers such that $a^{2}+b^{2}=8 a b$, find the value of $\left|\frac{a+b}{a-b}\right|$.
-/
theorem algebra_611463 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h: a^2 + b^2 = 8*a*b): abs ((a+b)/(a-b)) = sqrt (5 / 3) := by

  -- Take variable x = a - b and y = a - b to simplify calculation
  let x:ℝ := a+b
  let y:ℝ := a-b
  
  have h1: a^2 + b^2 = 8*a*b := by exact h

  -- Inverse tranform to get original expressions
  have ha: a = (x+y)/2 := by
    unfold x y
    ring_nf
  have hb: b = (x-y)/2 := by
    unfold x y
    ring_nf

  
  rw [ha, hb] at h
  field_simp at h

  -- Simpilfy expression in terms of x, y
  have h': (x^2 + y^2) = 4 * (x^2 - y^2) := by linarith
  have h'': 3*x^2 = 5*y^2 := by linarith
  
  -- The dominator is never zero
  have hneq: a ≠ b := by
    by_contra! w
    rw [w] at  h1
    ring_nf at h1
    have :b^2 = 0 := by  linarith
    have :b = 0 := pow_eq_zero this
    contradiction
  
  have hbneq: y ≠ 0 := by
    unfold y
    by_contra! weq
    have : a = b := by linarith
    contradiction
  
  rw [ha, hb]

  -- Calcuate |(a+b)/(a-b)| from x,y
  calc
    _ = abs (x/y) := by
      unfold x y
      field_simp
    _ = sqrt (5 / 3) := by
      have heq1: (x/y)^2 = 5/3 := by field_simp;linarith
      have ht: abs (x/y) = sqrt ((x/y)^2) := by
        rw [sqrt_sq_eq_abs _]
      rw [ht, heq1]
  
