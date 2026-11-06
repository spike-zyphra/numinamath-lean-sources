import Mathlib

theorem number_theory_388 (n : ℕ) (h1 : 3 ∣ n) (h2 : 5 ∣ n + 1) (h3 : 7 ∣ n + 2)
    (h4 : 100 ≤ n) (h5 : n + 2 ≤ 200) :
    n = 159 := by
  have h6 : n ≤ 198 := by linarith 
  interval_cases n <;> norm_num at h1 h2 h3 <;> omega