import Mathlib

theorem number_theory_153925 (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a + b + c = 2015) (h' : ∃ n, a = n ^ 2 + 1 ∧ b = (n + 1) ^ 2 + 1 ∧ c = (n + 2) ^ 2 + 1) :
    max (max a b) c = 676 := by
  rcases h' with ⟨n, ha1, hb1, hc1⟩
  rw [ha1] at h
  rw [hb1] at h
  rw [hc1] at h
  have eq1 : 3 * n ^ 2 + 6 * n + 8 = 2015 := by
    nlinarith
  have eq2 : 3 * n ^ 2 + 6 * n = 2007 := by
    omega
  have h4 : n ≤ 31 := by
    nlinarith
  have h5 : n ≤ 31 := h4
  interval_cases n <;> norm_num [ha1, hb1, hc1] at h ⊢ <;> omega