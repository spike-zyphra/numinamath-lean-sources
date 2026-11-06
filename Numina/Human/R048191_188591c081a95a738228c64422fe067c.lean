import Mathlib
open Real

/- How many ordered triples (a, b, c) of non-zero real numbers
   have the property that
   each number is the product of the other two?
   (A) 1 (B) 2 (C) 3 (D) 4 (E) 5
-/
theorem algebra_95809 (a b c : ℝ)
  (ha : a ≠ 0)      (hb : b ≠ 0)      (hc : c ≠ 0)
  (h1 : a = b * c)  (h2 : b = a * c)  (h3 : c = a * b)
: (a, b, c) = ( 1, 1, 1)
∨ (a, b, c) = ( 1,-1,-1)
∨ (a, b, c) = (-1,-1, 1)
∨ (a, b, c) = (-1, 1,-1) := by
  -- multiplying these three equations together
  have h := h1
  rw [← mul_left_inj' hb] at h
  rw (occs := .pos [3]) [h2] at h
  rw [← mul_left_inj' hc] at h
  rw (occs := .pos [4]) [h3] at h
  -- factorize the expression to get abc(abc-1)=0
  have h4:a*(b*c)*(a*(b*c)-1)=0:=by linarith only [h]
  -- as a,b,c are all non-zero we cannont have abc=0, so we have abc=1
  simp [ha,hb,hc] at h4
  -- substituting bc=a gives a=±1
  rw [← h1] at h4
  have h5:a*a=1:=by linarith only [h4]
  rw [mul_self_eq_one_iff] at h5
  -- discussing the value of a
  obtain ha1 | ha2 := h5
  -- if a=1
  · simp [ha1,h2] at *
    symm at h1
    -- simplifying the formulae gives b=c and bc=1
    -- so either b=c=1 or b=c=-1
    rw [mul_self_eq_one_iff] at h1
    obtain hc1 | hc2 := h1
    · left;norm_num [hc1]
    · right;left;norm_num [hc2]
  -- if a=-1
  · simp [ha2,h2] at *
    symm at h1
    -- simplifying the formulae gives -b=c and bc=-1
    -- so either b=1, c=-1 or b=-1, c=1
    rw [mul_self_eq_one_iff] at h1
    obtain hc1 | hc2 := h1
    · right;right;left;norm_num [hc1]
    · right;right;right;norm_num [hc2]