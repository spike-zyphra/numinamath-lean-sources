import Mathlib

/-
Lucas writes two distinct positive integers on a whiteboard. He decreases the smaller number by 20 and increases the larger number by 23 , only to discover the product of the two original numbers is equal to the product of the two altered numbers. Compute the minimum possible sum of the original two numbers on the board.
-/

theorem algebra_610650 : IsLeast {x:ℕ | ∃ a b : ℕ, a+b=x ∧ 0<a ∧ 0 < b ∧ a<b ∧ (((a:ℤ)-20) * (b+23) = a * b)} 321 := by
  unfold IsLeast; unfold lowerBounds
  constructor

  -- We first prove that 321 is valid.
  simp; use 160; use 161; simp

  -- Then we show that there is no better answer.
  simp; intro x a b apbeqx apos bpos alb h

  -- rewrite the equation to the following form.
  have eq : 23 * ((a:ℤ)-20) = 20 * b := by nlinarith

  -- Then, we get 23 ∣ b.
  have cla : 23 ∣ (b:ℤ) := by 
    have : 23 ∣ (20*(b:ℤ)) := by omega
    exact Int.dvd_of_dvd_mul_right_of_gcd_one this rfl
  
  -- Use a < b and eq to obtain 154 ≤ b.
  have lbf : 154 ≤ b := by omega

  have lb : 161 ≤ b := by linarith
  have la : 160 ≤ a := by nlinarith
  linarith

  