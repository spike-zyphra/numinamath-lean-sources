import Mathlib

/-In a certain college containing 1000 students, students may choose to major in exactly one of math, computer science, finance, or English. The diversity ratio $d(s)$ of a student $s$ is the defined as number of students in a different major from $s$ divided by the number of students in the same major as $s$ (including $s$ ). The diversity $D$ of the college is the sum of all the diversity ratios $d(s)$.
Determine all possible values of $D$.-/
theorem combinatorics_609679 :
    {D : ℕ | ∃ (n : Fin 4 → ℕ), (∑ i, n i) = 1000 ∧ D = ∑ s ∈ Finset.univ.filter (fun i => n i > 0), (1000 - n s)} = {0,1000,2000,3000} := by
  -- Prove set equality using extensionality.
  apply Set.ext
  intro D
  constructor
  · intro ⟨n, h_sum, h_D⟩
    -- Define $k$ as the number of majors with positive students.
    let k := (Finset.univ.filter fun i => n i > 0).card
    have h_k_pos : 0 < k := by
      by_contra h_zero
      push_neg at h_zero
      have h_all_zero : ∀ i : Fin 4, n i = 0 := by
        intro i
        by_contra h_nz
        have : i ∈ Finset.univ.filter fun j => n j > 0 := Finset.mem_filter.mpr ⟨Finset.mem_univ i, (by omega)⟩
        have h_k_zero : k = 0 := by omega
        have h_empty : Finset.univ.filter fun j => n j > 0 = ∅ := Finset.card_eq_zero.mp h_k_zero
        rw [h_empty] at this
        exact Finset.not_mem_empty i this
      have : ∑ i, n i = 0 := Finset.sum_eq_zero (fun i _ => h_all_zero i)
      linarith
    have h_D_eq : D = ∑ s ∈ Finset.univ.filter fun i => n i > 0, 1000 - ∑ s ∈ Finset.univ.filter fun i => n i > 0, n s := by
      rw [h_D]
      rw [Finset.sum_tsub_distrib]
      intro x hx
      have : n x ≤ ∑ i, n i := Finset.single_le_sum (fun i _ => Nat.zero_le (n i)) (Finset.mem_univ x)
      rw [h_sum] at this
      exact this
    have h_sum_k_1000 : ∑ s ∈ Finset.univ.filter fun i => n i > 0, 1000 = k * 1000 := Finset.sum_const 1000
    have h_sum_n : ∑ s ∈ Finset.univ.filter fun i => n i > 0, n s = 1000 := by
      rw [Finset.sum_filter_of_ne]
      · exact h_sum
      · intro i hi
        omega
    rw [h_sum_k_1000, h_sum_n] at h_D_eq
    -- Derive $D = (k-1)*1000$.
    have h_k_le_4 : k ≤ 4 := Finset.card_le_card (Finset.filter_subset _ Finset.univ)
    have h_k_ge_1 : k ≥ 1 := Nat.succ_le_of_lt h_k_pos
    have h_D_val : D = k * 1000 - 1000 := h_D_eq
    have h_D_multi : D = (k - 1) * 1000 := by
      rw [h_D_val]
      omega
    -- Use interval_cases to enumerate possible $k$ values ($1$ to $4$).
    interval_cases k
    · simp [h_D_multi]
    · simp [h_D_multi]
    · simp [h_D_multi]
    · simp [h_D_multi]
  -- Prove from right to left: construct n for each $D$ in ${0,1000,2000,3000}$.
  · intro h_D
    cases h_D with
    | inl h =>
      rw [h]
      use fun i => if i = 0 then 1000 else 0
      tauto
    | inr h_D =>
      cases h_D with
      | inl h =>
        rw [h]
        use fun i => if i < 2 then 500 else 0
        tauto
      | inr h_D =>
        cases h_D with
        | inl h =>
          rw [h]
          use fun i => if i < 3 then 333 + if i = 2 then 1 else 0 else 0
          tauto
        | inr h_D =>
          cases h_D with
          | refl =>
            use fun i => 250
            tauto
