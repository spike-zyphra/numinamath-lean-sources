import Mathlib

/- The fifth and eighth terms of a geometric sequence of real numbers are 7! and 8! respectively.  
What is the first term?

(A) 60(B) 75(C) 120(D) 225(E) 315-/
theorem algebra_93661 (a r : NNReal) (hr : r ≠ 0) (ha : a ≠ 0) (h5 : a * r^4 = Nat.factorial 7) (h8 : a * r^7 = Nat.factorial 8) :
a = 315:= by {
  /-
  This is a pretty straight-forward computation, since we have r^3 = (a * r^7) / (a * r^4) = 8! / 7! = 8. One 
  has to be careful with the types of the variables in the proof, because taking cube roots is certainly simpler
  if the base in positive. The argument below is somewhat shadowed by all the type-casting, but in essense is the
  calculation above
  -/
  suffices : r = 2

  -- We now show that it suffices to show that r = 2, by plugging this into the hypothesis h5 and rearranging.
  rw [this] at h5

  -- Lastly we show that r = 2 using the calculation above.
  have : Nat.factorial 7 = 5040 := by rfl
  calc a = a * 2^4 / 2^4 := by norm_num
       _ = Nat.factorial 7 / 2^4 := by norm_cast; norm_cast at h5; rw [h5]
       _ = 5040 / 2^4 := by rw [this]; norm_cast
       _ = 315 := by {field_simp; norm_cast}
  calc r = (r^(3 : ℝ))^((1/3 : ℝ)) := by rw [←NNReal.rpow_mul]; norm_num
       _ = ((a * r ^ (7 : ℝ))/(a * r ^ (4 : ℝ)))^((1/3 : ℝ)) := by rw [mul_div_mul_comm,div_self,one_mul,←NNReal.rpow_sub]; norm_num; exact hr; exact ha
       _ = (Nat.factorial 8 / Nat.factorial 7)^((1/3 : ℝ)) := by norm_num; rw [h5,h8]
       _ = 2 := by {
        rw [Nat.factorial_succ 7]
        norm_num
        rw [mul_div_cancel_right₀]
        have : (8 : NNReal) = 2 ^ (3 : ℝ) := by norm_cast
        rw [this]
        rw [←NNReal.rpow_mul]
        norm_num
        norm_cast
       } 
}