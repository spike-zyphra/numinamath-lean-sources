import Mathlib

theorem algebra_10561 (r : Set ℝ) (hr : r = setOf (fun (x : ℝ) => x ^ 3 + 3 * x ^ 2 - 10 * x = 0)) :
  (r = {0, 2, -5}) ∧ (∑x ∈ ({0, 2, -5} : Set ℝ), x) / ({0, 2, -5} : Set ℝ).ncard = -1 := by
  have h1 : r = {0, 2, -5} := by
    ext x
    simp [hr]
    constructor
    · -- Assume x is a root, need to show x in {0, 2, -5}
      intro h
      have h_eq : x ^ 3 + 3 * x ^ 2 - 10 * x = 0 := by
        simpa using h
      have : x * (x ^ 2 + 3 * x - 10) = 0 := by
        linarith [h_eq]
      cases' (mul_eq_zero.mp this) with hx hx
      · -- Case x = 0
        rw [hx]
        norm_num
      · -- Case x^2 + 3 * x - 10 = 0
        have h_eq2 : x ^ 2 + 3 * x - 10 = 0 := hx
        have : (x - 2) * (x + 5) = 0 := by
          nlinarith [h_eq2]
        cases' (mul_eq_zero.mp this) with h2 h5
        · -- x = 2
          have h_eq_x : x = (2 : ℝ) := by linarith
          rw [h_eq_x]
          norm_num
        · -- x = -5
          have h_eq_x : x = (-5 : ℝ) := by linarith
          rw [h_eq_x]
          norm_num
    · -- Show that {0, 2, -5} is subset of r
      rintro (rfl | rfl | rfl)
      · -- x = 0
        norm_num
      · -- x = 2
        norm_num
      · -- x = -5
        norm_num
  constructor
  · -- Show r = {0, 2, -5}
    exact h1
  · -- Show that the mean is -1
    norm_num [Finset.sum_insert, Finset.sum_singleton]