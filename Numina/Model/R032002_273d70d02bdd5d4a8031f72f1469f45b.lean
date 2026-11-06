import Mathlib

theorem number_theory_81 :
    Set.ncard {n : ℕ | 0 < n ∧ n < 100 ∧ ⌊(n / 2 : ℝ)⌋ + ⌊(n / 3 : ℝ)⌋ + ⌊(n / 6 : ℝ)⌋ = n} = 16 := by
  have h2 : {n : ℕ | 0 < n ∧ n < 100 ∧ ⌊(n / 2 : ℝ)⌋ + ⌊(n / 3 : ℝ)⌋ + ⌊(n / 6 : ℝ)⌋ = n} = Finset.filter (fun (n : ℕ) => 0 < n ∧ n < 100 ∧ n % 6 = 0) (Finset.Icc 0 99) := by 
    ext n
    simp
    constructor
    · -- First, the forward direction
      rintro ⟨hn1, hn2, heq⟩
      have h3 : n < 100 := by 
        omega 
      have h5 : n % 6 = 0 := by
        interval_cases n <;> norm_num at heq ⊢
        <;> omega 
      omega 
    · -- Now the reverse direction 
      rintro ⟨hn1, hn2, h3⟩
      have h4 : n < 100 := by 
        omega 
      have h5 : n % 6 = 0 := by 
        omega 
      constructor
      · -- Show n > 0
        omega
      constructor
      · -- Show n < 100
        omega
      · -- Show the equation 
        interval_cases n <;> norm_num at h5 ⊢
        <;> norm_num [Int.floor_eq_iff] at *
        <;> omega 
  rw [h2]
  rw [Set.ncard_coe_Finset]
  native_decide