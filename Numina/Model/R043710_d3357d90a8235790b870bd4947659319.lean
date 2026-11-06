import Mathlib

theorem number_theory_221547 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (hsum : x + y = 432) (hlcm : Nat.lcm x y + Nat.gcd x y = 7776) :
    x * y = 46620 := by
  have h2 : y = 432 - x := by
    omega

  rw [h2] at hlcm
  have h1 : x ≤ 432 := by
    omega

  interval_cases x <;> norm_num [Nat.lcm, Nat.gcd] at hlcm ⊢
    <;> omega