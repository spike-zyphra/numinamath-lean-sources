import Mathlib

theorem number_theory_174994 (n : ℕ) :
    ∃! m, m ∈ Finset.Icc n (n + 4) ∧ 5 ∣ m := by 
  have h1 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    omega 
  rcases h1 with (h | h | h | h | h)
  · -- Case n % 5 = 0
    use n
    constructor
    · -- Show that n ∈ [n, n + 4] ∧ 5 ∣ n
      constructor
      · -- Show that n ∈ [n, n + 4]
        simp [Finset.mem_Icc]
      · -- Show that 5 ∣ n
        omega 
    · -- Show that for any m' in [n, n + 4] with 5 ∣ m', m' = n
      intro m' 
      intro h'
      rcases h' with ⟨hm1, hm2⟩
      rw [Finset.mem_Icc] at hm1
      rcases hm1 with ⟨hm1l, hm1r⟩
      omega 
  · -- Case n % 5 = 1
    use n + 4 
    constructor
    · -- Show that n + 4 ∈ [n, n + 4] ∧ 5 ∣ (n + 4)
      constructor
      · -- Show that n + 4 ∈ [n, n + 4]
        simp [Finset.mem_Icc]
        all_goals omega 
      · -- Show that 5 ∣ (n + 4)
        omega 
    · -- Show that for any m' in [n, n + 4] with 5 ∣ m', m' = n + 4
      intro m' 
      intro h'
      rcases h' with ⟨hm1, hm2⟩
      rw [Finset.mem_Icc] at hm1
      rcases hm1 with ⟨hm1l, hm1r⟩
      omega 
  · -- Case n % 5 = 2
    use n + 3 
    constructor
    · -- Show that n + 3 ∈ [n, n + 4] ∧ 5 ∣ (n + 3)
      constructor
      · -- Show that n + 3 ∈ [n, n + 4]
        simp [Finset.mem_Icc]
        all_goals omega 
      · -- Show that 5 ∣ (n + 3)
        omega 
    · -- Show that for any m' in [n, n + 4] with 5 ∣ m', m' = n + 3
      intro m' 
      intro h'
      rcases h' with ⟨hm1, hm2⟩
      rw [Finset.mem_Icc] at hm1
      rcases hm1 with ⟨hm1l, hm1r⟩
      omega 
  · -- Case n % 5 = 3
    use n + 2 
    constructor
    · -- Show that n + 2 ∈ [n, n + 4] ∧ 5 ∣ (n + 2)
      constructor
      · -- Show that n + 2 ∈ [n, n + 4]
        simp [Finset.mem_Icc]
        all_goals omega 
      · -- Show that 5 ∣ (n + 2)
        omega 
    · -- Show that for any m' in [n, n + 4] with 5 ∣ m', m' = n + 2
      intro m' 
      intro h'
      rcases h' with ⟨hm1, hm2⟩
      rw [Finset.mem_Icc] at hm1
      rcases hm1 with ⟨hm1l, hm1r⟩
      omega 
  · -- Case n % 5 = 4
    use n + 1 
    constructor
    · -- Show that n + 1 ∈ [n, n + 4] ∧ 5 ∣ (n + 1)
      constructor
      · -- Show that n + 1 ∈ [n, n + 4]
        simp [Finset.mem_Icc]
        all_goals omega 
      · -- Show that 5 ∣ (n + 1)
        omega 
    · -- Show that for any m' in [n, n + 4] with 5 ∣ m', m' = n + 1
      intro m' 
      intro h'
      rcases h' with ⟨hm1, hm2⟩
      rw [Finset.mem_Icc] at hm1
      rcases hm1 with ⟨hm1l, hm1r⟩
      omega