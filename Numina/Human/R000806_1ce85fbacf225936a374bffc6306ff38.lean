import Mathlib

open Complex

/-Complex numbers $a,$ $b,$ $c$ form an equilateral triangle with side length 18 in the complex plane.  If $|a + b + c| = 36,$ find $|ab + ac + bc|.$-/
theorem calculus_15998 (a b c : ℂ) (h0 : ‖a - b‖ = 18) (h1 : ‖a - c‖ = 18)
(h2 : ‖b - c‖ = 18) (h3 : ‖a + b + c‖ = 36) :
‖a * b + a * c + b * c‖ = 432 := by
-- Apply the law of cosine to $a$, $b$ and $c$
  have := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle a b c
  repeat rw [dist_eq_norm] at this
  rw [norm_sub_rev] at h2
  rw [h0, h1, h2, EuclideanGeometry.angle.eq_1] at this
-- Apply angle_eq_abs_arg and cos_arg to find the value real part of $(a-b)/(c-b)$
  norm_num at this; rw [angle_eq_abs_arg] at this
  apply_fun (fun x => (648 - x) / 648) at this; norm_num at this; symm at this
  rw [cos_arg, ← norm_eq_abs, norm_div, h0, h2] at this; norm_num at this
-- For simpicity, denote $(a-b)/(c-b)$ by $z$ and prove two properties about it
  let z := (a - b) / (c - b)
  have rez : z.re = 1 / 2 := by simp only [z]; assumption
  have imz : z.im ^ 2 = 3 / 4 := by
    have : ‖z‖ ^ 2 = 1 := by simp only [z]; rw [norm_div, h0, h2]; norm_num
    rw [← normSq_eq_norm_sq, normSq] at this; norm_num at this
    rw [rez] at this; norm_num at this; rw [← pow_two] at this
    apply_fun (fun x => x - 1/4) at this; norm_num at this; assumption
-- Prove that the following identity about z
  have aux : z ^ 2 - z + 1 = 0 := by
    rw [← Complex.re_add_im z, rez]; norm_num
    rw [add_pow_two, ← sub_sub, mul_pow]; norm_num; norm_cast
    rw [imz]; norm_num; ring
-- Rewrite this identity and finish the final goals
  simp only [z, div_pow] at aux
  apply_fun (fun x => x * (c - b) ^ 2) at aux
  rw [zero_mul, add_mul, sub_mul, one_mul, div_mul_cancel₀] at aux
  nth_rw 2 [pow_two] at aux; rw [← mul_assoc, div_mul_cancel₀] at aux
  ring_nf at aux; rw [← neg_mul, add_sub] at aux
  apply_fun (fun x => x + 3 * (a * b + b * c + c * a)) at aux
  ring_nf at aux
  rw [show a*b*2+a*c*2+a^2+b*c*2+b^2+c^2=(a+b+c)^2 by ring] at aux
  rw [show a*b*3+a*c*3+b*c*3=3*(a*b+a*c+b*c) by ring] at aux
  apply_fun (fun x => ‖x‖/3) at aux
  rw [norm_pow, norm_mul, h3] at aux; norm_num at aux
  rw [norm_eq_abs]; symm; assumption
  all_goals intro; simp_all