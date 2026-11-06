import Mathlib

/-
3. If the length, width, and height of a rectangular prism are all prime numbers, and the sum of the areas of two adjacent sides is 341, then the volume of this rectangular prism $V=$ $\qquad$ .
-/

theorem number_theory_317323 (x y z : ℕ) (xp: Nat.Prime x)(yp: Nat.Prime y)(zp: Nat.Prime z) (h: x*y + x*z = 341): x*y*z = 638 := by 

  have : 2≤ x := by exact Nat.Prime.two_le xp
  have : 2≤ y := by exact Nat.Prime.two_le yp
  have : 2≤ z := by exact Nat.Prime.two_le zp
  have : 4 ≤ y+z := by omega

  --By x*y+x*z = 341, we have x ∣ 341, so there are four cases in total. We check them one by one.
  have : x ∣ 341 := by use (y+z); linarith
  have : 341 ≠ 0 := by linarith
  have xd: x ∣ 341 ∧ 341≠ 0 := by tauto
  rw [←Nat.mem_divisors] at xd
  have : Nat.divisors 341 = {1,11,31,341} := by native_decide
  rw [this] at xd
  simp at xd

  rcases xd with xe | xe | xe | xe

  -- case x=1
  linarith

  -- case x=11
  rw [xe] at h;
  have ypze: y+z = 31 := by linarith
  have : Even y ∨ Even z := by 
    by_contra oddyoddz; simp at oddyoddz
    have : Even (y + z) := by refine Odd.add_odd ?_ ?_;  exact oddyoddz.left; exact oddyoddz.right
    rw [ypze] at this
    have : Odd 31 := by use 15; norm_num
    have :¬ Even 31 := by exact Nat.not_even_iff.mpr rfl
    contradiction
  rcases this with eveny | evenz
  have ye: y = 2 := by exact (Nat.Prime.even_iff yp).mp eveny
  have ze: z = 29 := by omega
  rw [xe,ye,ze]
  have ze: z= 2 := by exact (Nat.Prime.even_iff zp).mp evenz
  have ye: y = 29 := by omega
  rw [xe,ye,ze]

  -- case x=31
  rw [xe] at h
  have ypze: y+z = 11 := by linarith
  have : Even y ∨ Even z := by 
    by_contra oddyoddz; simp at oddyoddz
    have : Even (y + z) := by refine Odd.add_odd ?_ ?_;  exact oddyoddz.left; exact oddyoddz.right
    rw [ypze] at this
    have : Odd 11 := by use 5; norm_num
    have :¬ Even 11 := by exact Nat.not_even_iff.mpr rfl
    contradiction
  rcases this with eveny | evenz
  have ye: y = 2 := by exact (Nat.Prime.even_iff yp).mp eveny
  have ze: z = 9 := by omega
  rw [ze] at zp; norm_num at zp
  have ze: z = 2 := by exact (Nat.Prime.even_iff zp).mp evenz
  have ye: y = 9 := by omega
  rw [ye] at yp; norm_num at yp

  -- case x=341
  rw [xe] at h
  have : y+z = 1 := by omega
  linarith