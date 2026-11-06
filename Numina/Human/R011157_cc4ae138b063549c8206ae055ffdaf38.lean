import Mathlib

/-
## Subject IV

Determine all pairs of natural numbers $\overline{a b}$ and $\overline{x y z}$, with $x<y<z$, such that

$$
\overline{a b} \cdot\left(x^{2}+y^{2}+z^{2}\right)=1 \cdot 2 \cdot 19 \cdot 53
$$

Note:

Working time: 2 hours

All subjects are mandatory

Each subject is graded from 0 to 7

No points are given ex officio

## MATHEMATICS OLYMPIAD

Local stage - Constanța, 23.02.2014

5th Grade

## Grading and marking rubric
-/
set_option maxHeartbeats 400000
theorem number_theory (a b x y z:ℕ) (ha: 0 < a) (hx: 0 < x) (au : a ≤ 9) (bu: b ≤ 9) (xu: x ≤ 9) (yu: y ≤ 9) (zu: z ≤ 9)  (hxyz: x < y ∧ y < z):
((10*a+b)*(x^2+y^2+z^2)=(1*2*19*53)) 
↔ 
(a=1∧b=9∧x=3∧y=4∧z=9) ∨ (a=3∧b=8∧x=1∧y=4∧z=6) ∨ (a=5∧b=3∧x=2∧y=3∧z=5) := by

  constructor

  intro h
  
  --We have 10*a+b ∣ 1*2*19*53. We enumerate all possibilities.
  let s := 10*a + b
  have sl : 10 ≤ s := by simp [s]; linarith
  have su : s ≤ 99 := by simp [s]; linarith
  have h' : s * (x^2+y^2+z^2) = 1*2*19*53 := h
  have hs : s ∣ 1*2*19*53 := by use x^2 + y^2 + z^2; rw [h]
  norm_num at hs
  have di2014: Nat.divisors 2014 =  {1,2,19,38,53,106,1007,2014 }:= by native_decide
  have : s ∈ Nat.divisors 2014 := by simp only [Nat.mem_divisors, hs]; norm_num
  rw [di2014] at this
  simp at this


  have xe: x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 := by omega
  have ye: y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 ∨ y = 8 ∨ y = 9 := by omega
  have ze: z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = 7 ∨ z = 8 ∨ z = 9 := by omega

  -- 10*a+b ∈ {1,2,19,38,53,106,1007,2014 }. Only 19,38,53 are valid.
  --For these three cases, we enumerate the possible values of x, y, z.
  rcases this with hs | hs | hs | hs | hs | hs | hs | hs  <;> simp [hs] at h'

  
  linarith
  linarith
  
  left
  have ae: a = 1 := by omega
  have be: b = 9 := by omega
  simp [ae,be]
  rcases xe with hx | hx | hx | hx | hx | hx | hx | hx | hx <;> 
  rcases ye with hy | hy | hy | hy | hy | hy | hy | hy | hy | hy <;>
  rcases ze with hz | hz | hz | hz | hz | hz | hz | hz | hz | hz <;>
  simp [hx,hy,hz] at h' ⊢ <;> 
  linarith
  
  have ae: a = 3 := by omega
  have be: b = 8 := by omega
  simp [ae,be]
  rcases xe with hx | hx | hx | hx | hx | hx | hx | hx | hx <;> 
  rcases ye with hy | hy | hy | hy | hy | hy | hy | hy | hy | hy <;>
  rcases ze with hz | hz | hz | hz | hz | hz | hz | hz | hz | hz <;>
  simp [hx,hy,hz] at h' ⊢ <;> 
  linarith

  have ae: a = 5 := by omega
  have be: b = 3 := by omega
  simp [ae,be]
  rcases xe with hx | hx | hx | hx | hx | hx | hx | hx | hx <;> 
  rcases ye with hy | hy | hy | hy | hy | hy | hy | hy | hy | hy <;>
  rcases ze with hz | hz | hz | hz | hz | hz | hz | hz | hz | hz <;>
  simp [hx,hy,hz] at h' ⊢ <;> 
  linarith


  linarith
  linarith
  linarith

  --For the other direction, just simple verification.
  intro h
  rcases h with (h | h | h) <;> simp [h]

