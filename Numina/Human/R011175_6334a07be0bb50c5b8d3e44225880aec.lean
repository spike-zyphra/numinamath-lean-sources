import Mathlib

/-
1. $[\mathbf{3}]$ If $a$ and $b$ are positive integers such that $a^{2}-b^{4}=2009$, find $a+b$.
-/

theorem number_theory_155115  (a b : ℤ) (apos : 0 < a) (bpos : 0 < b) (h: a^2 - b^4 = 2009) :  a + b = 47 := by 
  have : a^2 - b^4 = (a-b^2) * (a+b^2) := by ring
  rw [this] at h

  --We rewrite our equation to be $(a+b^2)(a-b^2)=2009 = 49 * 7^2$
  have : 0 < a + b^2 := by positivity
  have : 0 < a - b^2 := by nlinarith
  let i : ℕ := (a - b^2).toNat
  let j : ℕ := (a + b^2).toNat
  have hi: i = a - b^2 := by omega
  have hj: j = a + b^2 := by omega
  have : i ≤ j := by nlinarith
  have eq : i * j = 2009 := by zify; field_simp [hi,hj]; exact h
  have ile45: i ≤ 45 := by nlinarith

  have id : i ∣ 2009 := by use j; symm; exact eq
  have divi2009: Nat.divisors 2009 = {1,7,41,49,287,2009} := by native_decide
  have : i ∈ Nat.divisors 2009 := by simp [id]
  rw [divi2009] at this
  simp at this

  --Then, we enumerate all possibiliteis of a-b^2.
  rcases this with i1 | i7 | i41 | i49 | i287 | i2009
  have je: j = 2009 := by nlinarith
  rw [i1] at hi
  rw [je] at hj
  have : b ^ 2 = 1004 := by omega
  have : b < 32 := by nlinarith [pow_two b]
  have : 31 < b := by nlinarith 
  linarith

  have je: j = 287 := by nlinarith
  rw [i7] at hi
  rw [je] at hj
  have : b^2 = 140 := by omega
  have : b < 12 := by nlinarith [pow_two b]
  have : 11 < b := by nlinarith
  linarith

  have je: j = 49 := by nlinarith
  rw [i41] at hi
  rw [je] at hj
  have : a = 45 := by omega
  have : b^2 = 4 := by omega
  have : b=2:= by nlinarith
  linarith

  linarith
  linarith
  linarith

