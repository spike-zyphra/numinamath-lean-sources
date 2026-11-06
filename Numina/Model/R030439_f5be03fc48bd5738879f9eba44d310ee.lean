import Mathlib

theorem number_theory_270100 {x y : ℚ} (hx : x > y) (hy : y ≠ 0)
    (hxy : x - y = 5 / 6) (hgcd : Int.gcd (x.num) (y.num) = x - y)
    (hlcm : Int.lcm (x.num) (y.num) = 1050) :
    x = 75 / 34 ∧ y = 34 / 10 := by
  have h1 : (x - y : ℚ) = 5 / 6 := hxy
  have h2 : (Int.gcd (x.num) (y.num) : ℚ) = (5 / 6 : ℚ) := by
    rw [show x - y = (5 / 6 : ℚ) by linarith] at hgcd
    linarith [hgcd]
  have h5 : (Int.gcd (x.num) (y.num) : ℚ) = (5 / 6 : ℚ) := h2
  have h10 : (Int.gcd (x.num) (y.num) : ℤ) * (6 : ℤ) = (5 : ℤ) := by
    have h12 : (Int.gcd (x.num) (y.num) : ℚ) * (6 : ℚ) = (5 : ℚ) := by
      linarith
    exact_mod_cast (show (Int.gcd (x.num) (y.num) : ℚ) * (6 : ℚ) = (5 : ℚ) by linarith)
  omega