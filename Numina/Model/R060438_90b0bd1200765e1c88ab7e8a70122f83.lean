import Mathlib

theorem algebra_97657 {a : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (h4 : a 4 + a 7 + a 10 = 17) (hsum : ∑ i in Finset.Icc 4 14, a i = 77)
    (hk : a k = 13) :
    k = 18 := by
  rcases ha with ⟨d, had⟩
  have ha4 : a 4 = a 0 + d * (4 : ℕ) := had 4
  have ha7 : a 7 = a 0 + d * (7 : ℕ) := had 7
  have ha10 : a 10 = a 0 + d * (10 : ℕ) := had 10
  norm_num at ha4 ha7 ha10
  rw [ha4, ha7, ha10] at h4
  have hsum4 : ∑ i in Finset.Icc 4 14, a i = 11 * (a 0 + 9 * d) := by
    simp [Finset.sum_Icc_succ_top, Finset.sum_range_succ, had 4, had 5, had 6, had 7, had 8, had 9, had 10, had 11, had 12, had 13, had 14]
    <;> norm_num
    <;> ring
  rw [hsum4] at hsum
  have eq1 : a 0 + 9 * d = 7 := by
    nlinarith
  have eq2 : a 0 + 7 * d = 17 / 3 := by
    nlinarith
  have eq3 : d = 2 / 3 := by
    nlinarith [eq1, eq2]
  have eq4 : a 0 = 1 := by
    nlinarith [eq1, eq3]
  have eq5 : a k = a 0 + d * (k : ℕ) := had k
  rw [eq5] at hk
  rw [eq4, eq3] at hk
  have hk' : (k : ℝ) = (18 : ℝ) := by
    nlinarith
  have hk'' : k = 18 := by
    exact_mod_cast hk'
  exact_mod_cast hk''