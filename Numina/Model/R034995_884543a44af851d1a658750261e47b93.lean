import Mathlib

theorem number_theory_220004 :
    ¬∃ n : ℕ, ∀ k : ℕ, Odd n ∧ k ≥ 2 ∧ Prime (∑ i ∈ Finset.range k, (n + 2 * i)) := by

  rintro ⟨n, hn⟩ 
  have h1 := hn 0
  norm_num at h1
  all_goals tauto