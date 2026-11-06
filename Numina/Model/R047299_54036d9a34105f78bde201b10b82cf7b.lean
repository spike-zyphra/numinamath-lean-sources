import Mathlib

theorem number_theory_355 (s : Finset ℕ) (hs : s = {n : ℕ | 0 < n ∧ n < 100 ∧ 6 ∣ (2 * n ^ 2 - 3 * n - 2 : ℤ)}) :
    ∑ x in s, x = 1634 := by
  have hz : {n : ℕ | 0 < n ∧ n < 100 ∧ 6 ∣ (2 * n ^ 2 - 3 * n - 2 : ℤ)} = Finset.filter (fun (n : ℕ) => 0 < n ∧ n < 100 ∧ 6 ∣ (2 * (n : ℤ) ^ 2 - 3 * (n : ℤ) - 2)) (Finset.Icc 0 100) := by
    ext n
    simp
    <;> try { tauto }
    <;> try { 
      have h4 : ∀ (n : ℕ), (↑n : ℤ) = (n : ℤ) := by
        intro n
        rfl
      simp [h4, Finset.filter] at *
      <;> try { tauto }
    }
    all_goals try omega
  have h2 : s = Finset.filter (fun (n : ℕ) => 0 < n ∧ n < 100 ∧ 6 ∣ (2 * (n : ℤ) ^ 2 - 3 * (n : ℤ) - 2)) (Finset.Icc 0 100) := by
    have h1 : {n : ℕ | 0 < n ∧ n < 100 ∧ 6 ∣ (2 * n ^ 2 - 3 * n - 2 : ℤ)} = Finset.filter (fun (n : ℕ) => 0 < n ∧ n < 100 ∧ 6 ∣ (2 * (n : ℤ) ^ 2 - 3 * (n : ℤ) - 2)) (Finset.Icc 0 100) := hz
    have h5 : (↑s : Set ℕ) = {n : ℕ | 0 < n ∧ n < 100 ∧ 6 ∣ (2 * n ^ 2 - 3 * n - 2 : ℤ)} := by
      exact_mod_cast hs
    have h6 : (s : Set ℕ) = Finset.filter (fun (n : ℕ) => 0 < n ∧ n < 100 ∧ 6 ∣ (2 * (n : ℤ) ^ 2 - 3 * (n : ℤ) - 2)) (Finset.Icc 0 100) := by
      rw [show (↑s : Set ℕ) = {n : ℕ | 0 < n ∧ n < 100 ∧ 6 ∣ (2 * n ^ 2 - 3 * n - 2 : ℤ)} by exact_mod_cast hs]
      rw [h1]
    have h7 : s = Finset.filter (fun (n : ℕ) => 0 < n ∧ n < 100 ∧ 6 ∣ (2 * (n : ℤ) ^ 2 - 3 * (n : ℤ) - 2)) (Finset.Icc 0 100) := by
      exact_mod_cast h6
    exact h7
  rw [h2]
  <;> try { 
    simp [Finset.filter] at *
    <;> try { native_decide }
  }
  <;> try { 
    simp [Finset.sum_filter, Finset.sum_range_succ, Finset.filter] at *
    <;> try { native_decide }
  }
  all_goals try native_decide