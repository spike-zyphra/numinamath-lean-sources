import Mathlib


theorem algebra_93282 {x : ℕ → ℕ} (h : ∃ k, ∀ n, x (n + 2) - x n = k * x (n + 1))
    (h1 : x 1994 = 39) (h2 : x 1995 = 60) (h3 : x 1997 = 123) :
    x 1996 = 84 := by
  rcases h with ⟨k, hk⟩
  have eq1 := hk 1994
  have eq2 := hk 1995
  norm_num [h1, h2, h3] at eq1 eq2
  all_goals
  have eq3 : (k : ℕ) * (x 1996 : ℕ) = 63 := by
    omega
  have eq4 : x 1996 - 39 = 60 * k := by
    omega
  have h4 : k ≤ 1 := by
    by_contra h5
    push_neg at h5
    have h5' : k > 1 := by omega
    have h6 : k ≥ 2 := by omega
    have h7 : (k : ℕ) * (x 1996 : ℕ) = 63 := by
      omega
    have h8 : x 1996 ≤ 31 := by
      nlinarith
    have h9 : x 1996 ≥ 159 := by
      omega
    omega
  interval_cases k <;> omega