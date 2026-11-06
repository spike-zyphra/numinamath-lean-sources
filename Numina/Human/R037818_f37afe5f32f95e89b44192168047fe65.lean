import Mathlib
import Init.Data.Int

open Classical

/- Al walks down to the bottom of an escalator that is moving up and he counts 150 steps. His friend, Bob, walks up to the top of the escalator and counts 75 steps. If Al's speed of walking (in steps per unit time) is three times Bob's walking speed, how many steps are visible on the escalator at a given time? (Assume that this value is constant.)
-/

/- Let the total number of steps be $x$,
       the speed of the escalator be $e$,
       the speeds of Al and Bob be $a$ and $b$ respectively,
       the times taken by Al and Bob be $a_t$ and $b_t$ respectively. -/
theorem algebra_697 (x e a b aₜ bₜ : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (he : e ≠ 0) (hat : 150 = a * aₜ) (hbt : 75 = b * bₜ) (heat : 150 - x = e * aₜ) (hebt : x - 75 = e * bₜ) (hab : a = 3 * b) : (x = 120) := by

  /- Find the relations between a and e, and b and e, in terms of x. -/
  have hea : ((150 - x) / 150 = e / a) := by
    have hea1 : 150 / a = aₜ := by
      rw [←mul_comm] at hat
      exact div_eq_of_eq_mul ha hat
    have hea2 : (150 - x) / e = aₜ := by
      rw [←mul_comm] at heat
      exact div_eq_of_eq_mul he heat
    have hea3 : (150 - x) / e = 150 / a := Eq.trans hea2 (Eq.symm hea1)
    have hea4 := mul_eq_mul_of_div_eq_div (150 - x) 150 he ha hea3
    rw [mul_comm 150 e] at hea4
    have hea5 := Eq.trans (div_mul_eq_mul_div (150 - x) 150 a) (div_eq_of_eq_mul (by decide) hea4)
    exact Eq.symm <| div_eq_of_eq_mul ha (Eq.symm hea5)

  have heb : ((x - 75) / 75 = e / b) := by
    have heb1 : 75 / b = bₜ := by
      rw [←mul_comm] at hbt
      exact div_eq_of_eq_mul hb hbt
    have heb2 : (x - 75) / e = bₜ := by
      rw [←mul_comm] at hebt
      exact div_eq_of_eq_mul he hebt
    have heb3 : (x - 75) / e = 75 / b := Eq.trans heb2 (Eq.symm heb1)
    have heb4 := mul_eq_mul_of_div_eq_div (x - 75) 75 he hb heb3
    rw [mul_comm 75 e] at heb4
    have heb5 := Eq.trans (div_mul_eq_mul_div (x - 75) 75 b) (div_eq_of_eq_mul (by decide) heb4)
    exact Eq.symm <| div_eq_of_eq_mul hb (Eq.symm heb5)

  /- Substitute a/e = 3 * b/e and equate the two expressions for b/e. -/
  have hx : ((150 - x) / 150 = (x - 75) / (75 * 3)) := by
    rw [hab] at hea
    rw [mul_comm] at hea
    have heb' := Eq.trans hea <| Eq.symm <| div_div e b 3
    rw [←heb] at heb'
    exact Eq.trans heb' <| div_div (x - 75) (75 : ℚ) 3

  /- Carry out arithmetic simplifications. -/
  have hx2 : (150 - x) * 225 = (x - 75) * 150 := by
    norm_num at hx
    exact mul_eq_mul_of_div_eq_div (150 - x) (x - 75) (by decide) (by decide) hx

  rw [mul_sub_right_distrib 150 x 225] at hx2
  rw [mul_sub_right_distrib x 75 150] at hx2
  norm_num at hx2
  have hx3 := eq_add_of_sub_eq hx2
  rw [add_comm, ←add_sub_assoc] at hx3
  have hx4 := add_eq_of_eq_sub hx3
  rw [←mul_add] at hx4
  norm_num at hx4
  have hx5 := div_eq_of_eq_mul (by decide) hx4
  norm_num at hx5
  exact Eq.symm hx5