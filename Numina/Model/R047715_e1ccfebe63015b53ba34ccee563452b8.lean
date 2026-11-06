import Mathlib

theorem number_theory_51290 (m n : ℤ) (hm : 0 < m) (hn : 0 < n)
    (h1 : 2 * m ∣ 3 * n - 2) (h2 : 2 * n ∣ 3 * m - 2) :
    (m = 2 ∧ n = 2) ∨ (m = 10 ∧ n = 14) ∨ (m = 14 ∧ n = 10) := by
  rcases h1 with ⟨k, hk⟩
  rcases h2 with ⟨l, hl⟩
  have eq1 : 3 * n - 2 = 2 * k * m := by
    linarith
  have eq2 : 3 * m - 2 = 2 * l * n := by
    linarith
  have h3 : k > 0 := by
    nlinarith [show 0 < m from hm, show 0 < n from hn]
  have h4 : l > 0 := by
    nlinarith [show 0 < m from hm, show 0 < n from hn]
  have h5 : k ≤ 3 := by
    nlinarith [show 0 < m from hm, show 0 < n from hn, sq_nonneg (m - n), sq_nonneg (2 * m - 3 * n), sq_nonneg (2 * n - 3 * m), sq_pos_of_pos hm, sq_pos_of_pos hn]
  have h6 : l ≤ 3 := by
    nlinarith [show 0 < m from hm, show 0 < n from hn, sq_nonneg (m - n), sq_nonneg (2 * m - 3 * n), sq_nonneg (2 * n - 3 * m), sq_pos_of_pos hm, sq_pos_of_pos hn]
  interval_cases k <;> interval_cases l <;> omega