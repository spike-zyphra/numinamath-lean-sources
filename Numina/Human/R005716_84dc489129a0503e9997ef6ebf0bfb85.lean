import Mathlib

theorem number_theory_609554 :
    {(k, m, n) : ℕ × ℕ × ℕ | k ≤ 100 ∧ m ≤ 100 ∧ n ≤ 100 
    ∧ 2 ^ m * n - 2 ^ n * m = 2 ^ k
  }.ncard = 22 := by 
  
  have h1 : {(k, m, n) : ℕ × ℕ × ℕ | k ≤ 100 ∧ m ≤ 100 ∧ n ≤ 100 
      ∧ 2 ^ m * n - 2 ^ n * m = 2 ^ k
  } = Finset.filter (fun s : ℕ × ℕ × ℕ => 
      s.1 ≤ 100 ∧ s.2.1 ≤ 100 ∧ s.2.2 ≤ 100 ∧ 2 ^ s.2.1 * s.2.2 - 2 ^ s.2.2 * s.2.1 = 2 ^ s.1
  ) (Finset.Icc (0, 0, 0) (100, 100, 100)) := by
    ext ⟨k, m, n⟩
    simp 
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide

  