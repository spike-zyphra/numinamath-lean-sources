import Mathlib

theorem algebra_195876 {A m n p : ℝ} (hA : A > 0 ∧ A ≠ 1) (hm : m > 0 ∧ m ≠ 1)
    (hn : n > 0 ∧ n ≠ 1) (hp : p > 0 ∧ p ≠ 1) :
    Real.logb m A * Real.logb n A + Real.logb n A * Real.logb p A +
    Real.logb p A * Real.logb m A =
    Real.logb A (m * n * p) * Real.logb p A * Real.logb n A * Real.logb m A := by

  have h1 : Real.logb m A = Real.log A / Real.log m := by
    field_simp [Real.logb]

  have h2 : Real.logb n A = Real.log A / Real.log n := by
    field_simp [Real.logb]

  have h3 : Real.logb p A = Real.log A / Real.log p := by
    field_simp [Real.logb]

  have h4 : Real.logb A (m * n * p) = (Real.log (m * n * p)) / Real.log A := by
    field_simp [Real.logb]

  have h5 : Real.log (m * n * p) = Real.log m + Real.log n + Real.log p := by
    simp [Real.log_mul, hm.1.ne.symm, hn.1.ne.symm, hp.1.ne.symm]

  rw [h1, h2, h3, h4, h5]

  have h6 : Real.log A ≠ 0 := by
    have h1 : A > 0 := hA.1
    have h2 : A ≠ 1 := hA.2
    exact Real.log_ne_zero_of_pos_of_ne_one h1 h2

  have h7 : Real.log m ≠ 0 := by
    have hm1 : m > 0 := hm.1
    have hm2 : m ≠ 1 := hm.2
    exact Real.log_ne_zero_of_pos_of_ne_one hm1 hm2

  have h8 : Real.log n ≠ 0 := by
    have hn1 : n > 0 := hn.1
    have hn2 : n ≠ 1 := hn.2
    exact Real.log_ne_zero_of_pos_of_ne_one hn1 hn2

  have h9 : Real.log p ≠ 0 := by
    have hp1 : p > 0 := hp.1
    have hp2 : p ≠ 1 := hp.2
    exact Real.log_ne_zero_of_pos_of_ne_one hp1 hp2

  field_simp [h6, h7, h8, h9]
  <;> ring