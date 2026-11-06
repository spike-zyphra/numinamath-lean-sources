import Mathlib
open Real
open scoped BigOperators

theorem algebra_2317 :
  IsGreatest {t : ℚ | ∃ x y m n : ℚ, x^2 + y^2 = 8 ∧ m^2 + n^2 = 8 ∧ t = x * y + m * n} 8 := by
  constructor
  · -- Show that 8 can be achieved
    use 2, 2, 2, 2
    norm_num
  · -- Show that for any t in the set, t ≤ 8
    intro t ht
    rcases ht with ⟨x, y, m, n, hx, hm, ht⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (m - n), sq_nonneg (x + y), sq_nonneg (m + n)]