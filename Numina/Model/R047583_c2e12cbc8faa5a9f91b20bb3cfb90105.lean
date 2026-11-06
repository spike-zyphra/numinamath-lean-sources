import Mathlib

theorem number_theory_317072 :
    Set.ncard {a : (Fin 3 → ℕ) | ∀ i, a i ∈ Finset.Icc 1 10 ∧ 9 ∣ (a 0 ^ 3 + a 1 ^ 3 + a 2 ^ 3)} = 243 := by
  have h1 : {a : (Fin 3 → ℕ) | ∀ i, a i ∈ Finset.Icc 1 10 ∧ 9 ∣ (a 0 ^ 3 + a 1 ^ 3 + a 2 ^ 3)} = Finset.filter (fun (a : Fin 3 → ℕ) => ∀ i, a i ∈ Finset.Icc 1 10 ∧ 9 ∣ (a 0 ^ 3 + a 1 ^ 3 + a 2 ^ 3)) (Finset.Icc (fun i => (1 : ℕ)) (fun i => (10 : ℕ)) ) := by
    ext a
    simp [Finset.mem_Icc]
    <;> try { aesop }
    <;> try { 
      intro h
      have h1 : ∀ i, 1 ≤ a i := by
        intro i
        have h2 := h i
        simp at h2 ⊢
        omega
      have h2 : ∀ i, a i ≤ 10 := by
        intro i
        have h3 := h i
        simp at h3 ⊢
        omega
      have h3 : a 0 ≥ 1 := by apply h1 0
      have h4 : a 1 ≥ 1 := by apply h1 1
      have h5 : a 2 ≥ 1 := by apply h1 2
      have h6 : a 0 ≤ 10 := by apply h2 0
      have h7 : a 1 ≤ 10 := by apply h2 1
      have h8 : a 2 ≤ 10 := by apply h2 2
      all_goals try { tauto }
      <;> try { omega }
    }
    <;> try { 
      intro h
      have h1 : ∀ i, 1 ≤ a i := by
        have h2 := h.1
        have h3 := h.2
        intro i
        fin_cases i <;> simp [Finset.mem_Icc] at h2 h3 ⊢ <;> omega
      have h2 : ∀ i, a i ≤ 10 := by
        have h3 := h.1
        have h4 := h.2
        intro i
        fin_cases i <;> simp [Finset.mem_Icc] at h3 h4 ⊢ <;> omega
      intro i
      have h3 := h1 i
      have h4 := h2 i
      simp [Finset.mem_Icc] at *
      <;> tauto
      <;> try { omega }
      <;> try { 
        tauto
        <;> omega
      }
    }
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide
  all_goals try { native_decide <;> try tauto <;> try { tauto <;> omega } }