import Mathlib

theorem algebra_97791 {a b c p : ℝ} (ha : a ≠ 0) (hp : p ≠ 0)
  (hv0 : a * p ^ 2 + b * p + c = p)
  (hv1 : p = - b / (2 * a))
  (hi : c = -p) :
b = 4 := by
  -- obtain the expression of a*2
  rw [← mul_left_inj' ((by simp [ha]):2*a≠0),
      ← mul_assoc,mul_comm,
      ← div_left_inj' ((by simp [hp]):p*2≠0)] at hv1
  simp [ha,hp] at hv1
  rw [← div_div,← mul_left_inj' ((by simp):(2:ℝ)≠0)] at hv1
  simp at hv1
  -- substituting (p,p) in the parabola
  -- using the expression of a*2 to simplify
  rw [← mul_left_inj' ((by simp):(2:ℝ)≠0)] at hv0
  repeat rw [add_mul] at hv0
  rw [mul_comm,← mul_assoc,mul_comm 2 a,hv1,hi,pow_two,← mul_assoc,div_mul,div_self hp,div_one] at hv0
  have hh:p*(b-4)=0;linarith
  -- since it is given that p≠0, then b = 4
  simp at hh
  cases hh
  · contradiction
  · linarith