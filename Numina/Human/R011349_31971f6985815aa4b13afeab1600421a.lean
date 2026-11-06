import Mathlib

/-
If positive integers $a$, $b$ satisfy the equation $a+\frac{(a+b)(a+b-1)}{2}=2009$, then $a=$ ______ , $b=$ ______ .
-/

theorem algebra_625547 (a b : ℤ) (ha: 0 < a) (hb: 0 < b): a + (a + b) * (a + b - 1) / (2:ℝ) = 2009 ↔ (a=56 ∧ b=7) := by

  constructor
  intro h
  
  have : 0 < (a:ℝ) := by norm_cast
  have : 0 < (b:ℝ) := by norm_cast

  --Letting k = a + b. Using our assumption, we have 2009 < k*(k+1)/2 and k*(k-1)/2 < 2009.
  let k : ℤ := a + b
  have lb : 4018 < k * (k+1) := by 
    simp [k]
    rify
    field_simp at h ⊢
    ring_nf at h ⊢
    rw [← h]
    field_simp
    nlinarith

  have ub : k*(k-1) < 4018 := by
    simp [k]
    rify
    nlinarith

  --The only positive integer solution to this is k = 63.
  --Putting it back to our assumption, we get a = 56 and b = 7.
  have ke: k = 63 := by nlinarith
  field_simp at h
  norm_cast at h
  have apbe: a+b = 63 := by simp [k] at ke; exact ke
  rw [apbe] at h
  norm_num at h
  have ae : a = 56 := by linarith
  have be : b = 7 := by linarith
  tauto

  --The other direction is simple calculation.
  intro ⟨ae,be⟩
  rw [ae,be]
  simp
  norm_num