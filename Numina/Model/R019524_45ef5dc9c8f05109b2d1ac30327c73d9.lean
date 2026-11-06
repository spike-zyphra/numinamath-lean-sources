import Mathlib

theorem algebra_316028 {f : ℕ → ℕ} (hf : ∀ n, n ≥ 1000 → f n = n - 3) (hf' : ∀ n, n < 1000 → f n = f (f (n + 7))) : f 90 = 999 := by

  have h1 : f 998 = 999 := by
    have h1 : f 1002 = 999 := by
      specialize hf 1002 (by norm_num)
      norm_num [hf]
    have h2 : f 1005 = 1002 := by 
      specialize hf 1005 (by norm_num)
      norm_num [hf]

    have h3 : f 998 = f (f 1005) := by
      apply hf' 998 (by norm_num)

    rw [h3]
    rw [h2]
    exact h1

  have h3 : f 997 = 998 := by
    have h4 : f 1004 = 1001 := by
      specialize hf 1004 (by norm_num)
      norm_num [hf]

    have h5 : f 1001 = 998 := by 
      specialize hf 1001 (by norm_num)
      norm_num [hf]

    have h6 : f 997 = f (f 1004) := by
      apply hf' 997 (by norm_num)

    rw [h6]
    rw [h4]
    exact h5

  simp [hf', hf,  h1, h3]
  all_goals try { native_decide }