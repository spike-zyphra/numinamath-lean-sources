import Mathlib

theorem algebra_254609 (M W : ℕ) (hM : M ≠ 0) (hW : W ≠ 0)
    (hM1 : M * 3 = W * 2) (hM2 : M > 0) (hW2 : W > 0)
    (hM3 : M * 37 + W * 42 = (M + W) * x) :
    x = 40 := by
  have h1 : M * 3 = W * 2 := hM1
  -- Total age: 37 * M + 42 * W
  have eq1 : M * 37 + W * 42 = (M + W) * x := by
    exact_mod_cast hM3
  -- Total people: M + W
  -- Total age = M * 37 + W * 42 = 100 * M
  -- Total people = M + W = 2.5 * M
  -- Average = Total age / Total people = 100/2.5 = 40
  have h4 : x = 40 := by
    nlinarith [hM3, hM1, show M > 0 by linarith, show W > 0 by linarith]
  exact_mod_cast h4