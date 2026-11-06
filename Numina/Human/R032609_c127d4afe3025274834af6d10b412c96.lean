import Mathlib

open Real

/- 7.201. $3 \lg 2+\lg \left(2^{\sqrt{x-1}-1}-1\right)=\lg \left(0.4 \sqrt{2^{\sqrt{x-1}}}+4\right)+1$. -/
theorem algebra_167239 (x : ℝ) (hx : 2 < x) :
    3 * logb 10 2 + logb 10 (2 ^ (sqrt (x - 1) - 1) - 1) =
    logb 10 (0.4 * sqrt (2 ^ (sqrt (x - 1))) + 4) + 1 ↔ x = 17 := by
  constructor
  rotate_left
  -- let's show the result is valid first
  intro h; rw [h]; norm_num
  rw [show (16:ℝ)=4^2 by norm_num]; simp; norm_num
  rw [show (16:ℝ)=4^2 by norm_num]; simp; norm_num
  rw [logb_div (by norm_num) (by norm_num), show (28:ℝ)=2*2*7 by norm_num, logb_mul (by norm_num) (by norm_num), logb_mul (by norm_num) (by norm_num)];
  suffices 0 = logb 10 2 + logb 10 2 + logb 10 7 - logb 10 5 + 1 - 3 * logb 10 2 - logb 10 7 by linarith
  ring_nf; apply Eq.symm
  calc 1 + (-logb 10 2 - logb 10 5)
    _ = 1 - (logb 10 2 + logb 10 5) := by ring_nf
    _ = 1 - (logb 10 (2*5)) := by rw [Real.logb_mul (by norm_num) (by norm_num)]
    _ = 0 := by norm_num

  -- for later we'll also show a quick inequality to be able to convert terms
  have h': (2:ℝ) ^ √(x - 1) > 2 := by
    simp; suffices 1 < (2:ℝ) ^ (√(x - 1) - 1) by rw [rpow_sub (by norm_num), rpow_one] at this; linarith
    apply (Real.one_lt_rpow_iff_of_pos (x:=2) (by norm_num)).mpr
    left
    constructor
    norm_num
    simp
    apply lt_sqrt_of_sq_lt; linarith
  -- now let's solve the equation
  intro h
  -- let's write both sides as logs to get rid of them
  rw [← logb_rpow_eq_mul_logb_of_pos (by norm_num), ← logb_mul (by norm_num) (by rw [rpow_sub (by norm_num)];linarith)] at h
  conv_rhs at h=>
    calc _
    _ = logb 10 (0.4 * √(2 ^ √(x - 1)) + 4) + logb 10 10 := by norm_num
    _ = logb 10 (10 * (0.4 * √(2 ^ √(x - 1)) + 4)) := by rw [Real.logb_mul (by norm_num) (by have h: 0 < √(2 ^ √(x - 1)):= (by simp; linarith);linarith)]; ring_nf
  apply congr_arg (fun x => (10:ℝ)^x) at h
  rw [rpow_logb (by norm_num) (by norm_num) (by apply mul_pos; norm_num; rw [rpow_sub (by norm_num)]; linarith), rpow_logb (by norm_num) (by norm_num) (by norm_num; apply add_pos; apply mul_pos; norm_num; simp; linarith; norm_num)] at h
  -- now we convert into quadratic by labellying y = 2^(√(x - 1)/2)
  let q:∃ y:ℝ, y = (2:ℝ)^((√(x-1)/2)) := by
    simp only [exists_eq]
  obtain ⟨y, ydef⟩ := q
  rw [
    sqrt_eq_rpow (x:=(2 ^ √(x - 1))), ← rpow_mul (by norm_num), rpow_sub (by norm_num),
    show 2 ^ √(x - 1)=(√(2 ^ √(x - 1)))^2 by (rw [sq_sqrt (by linarith)]),
    sqrt_eq_rpow, ← rpow_mul (by norm_num),
    show √(x - 1) * (1 / 2) = √(x-1)/2  by ring_nf, ← ydef,
    show 10 * (0.4 * y + 4) = 4 * y + 40 by ring_nf,
    show (2:ℝ) ^ (3:ℝ) * (y ^ 2 / 2 ^ (1:ℝ) - 1) = 4 * y^2 - 8 by norm_num; ring_nf
  ] at h;
  apply congr_arg (fun x => (x - 4*y - 40)/4) at h; ring_nf at h
  -- and solve it
  have sol := (quadratic_eq_zero_iff (a:=(1:ℝ)) (b:=(-1:ℝ)) (c:=-12) (by norm_num) (s:=7) (by unfold discrim; ring_nf) y).mp
  ring_nf at h sol; specialize sol h
  -- we get two solutions, let's go back from y to x
  cases' sol with sol1 sol2
  · rw [sol1] at ydef
    -- log both sides
    apply congr_arg (fun x => logb 2 x) at ydef
    rw [show (4:ℝ)=2^(2:ℝ) by norm_num, logb_rpow (by norm_num) (by norm_num), logb_rpow (by norm_num) (by norm_num)] at ydef
    apply congr_arg (fun x =>(2*x)^2) at ydef
    norm_num at ydef; ring_nf at ydef; rw [sq_sqrt (by linarith)] at ydef
    linarith
  · -- power of 2 is negative, this is a contradiction
    exfalso
    rw [sol2] at ydef
    have h2:= rpow_pos_of_pos (show 0<2 by norm_num) (√(x - 1) / 2)
    rw [← ydef] at h2
    linarith