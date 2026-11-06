import Mathlib

theorem number_theory_139216 (k : ℕ) (m : ℕ) (hk : 0 < k) (hm : Odd m) :
    ∃ n : ℕ, 0 < n ∧ 2 ^ k ∣ (n ^ n - m) := by 
  use 1
  constructor 
  · -- Show $n$ is positive
    norm_num
  · -- Show $2^k \mid (1^1 - m)$
    have h3 : Odd m := hm
    rcases h3 with ⟨t, ht⟩
    have h5 : (1: ℕ) ^ 1 - m = 0 := by
      omega
    rw [h5]
    all_goals 
      simp at *
      <;> all_goals omega