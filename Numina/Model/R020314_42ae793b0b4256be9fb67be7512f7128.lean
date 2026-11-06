import Mathlib

theorem number_theory_195064 (x : ℕ) (hx : x ∈ Finset.Icc 10 99) :
    {i | (i = 1 ∧ 3 ∣ x) ∨ (i = 2 ∧ 5 ∣ x) ∨ (i = 3 ∧ 9 ∣ x) ∨
      (i = 4 ∧ 15 ∣ x) ∨ (i = 5 ∧ 25 ∣ x) ∨ (i = 6 ∧ 45 ∣ x)}.encard = 3 ↔
    x = 15 ∨ x = 30 ∨ x = 60 := by
  rw [Finset.mem_Icc] at hx
  rcases hx with ⟨hx1, hx2⟩
  constructor
  · -- Forward: if exactly 3 divisibility statements are true, then x is 15, 30, 60.
    intro h
    have h1 : x ≤ 99 := by linarith
    have h2 : {i | (i = 1 ∧ 3 ∣ x) ∨ (i = 2 ∧ 5 ∣ x) ∨ (i = 3 ∧ 9 ∣ x) ∨
      (i = 4 ∧ 15 ∣ x) ∨ (i = 5 ∧ 25 ∣ x) ∨ (i = 6 ∧ 45 ∣ x)} = 
        Finset.filter (fun i => (i = 1 ∧ 3 ∣ x) ∨ (i = 2 ∧ 5 ∣ x) ∨ (i = 3 ∧ 9 ∣ x) ∨
          (i = 4 ∧ 15 ∣ x) ∨ (i = 5 ∧ 25 ∣ x) ∨ (i = 6 ∧ 45 ∣ x)) (Finset.Icc 1 6) := by
      ext i
      simp
      omega
    rw [h2] at h
    rw [Set.encard_coe_eq_coe_finsetCard] at h
    interval_cases x <;> try { norm_num at h ⊢ <;> try { tauto } }
  · -- Backward: if x is 15, 30, 60, then exactly 3 divisibility statements are true.
    rintro (rfl | rfl | rfl)
    · -- x = 15
      have h1 : {i | (i = 1 ∧ 3 ∣ (15 : ℕ)) ∨ (i = 2 ∧ 5 ∣ (15 : ℕ)) ∨ (i = 3 ∧ 9 ∣ (15 : ℕ)) ∨
        (i = 4 ∧ 15 ∣ (15 : ℕ)) ∨ (i = 5 ∧ 25 ∣ (15 : ℕ)) ∨ (i = 6 ∧ 45 ∣ (15 : ℕ))} = {1, 2, 4} := by
        ext i
        simp
        omega
      rw [h1]
      rw [Set.encard]
      simp
    · -- x = 30
      have h1 : {i | (i = 1 ∧ 3 ∣ (30 : ℕ)) ∨ (i = 2 ∧ 5 ∣ (30 : ℕ)) ∨ (i = 3 ∧ 9 ∣ (30 : ℕ)) ∨
        (i = 4 ∧ 15 ∣ (30 : ℕ)) ∨ (i = 5 ∧ 25 ∣ (30 : ℕ)) ∨ (i = 6 ∧ 45 ∣ (30 : ℕ))} = {1, 2, 4} := by
        ext i
        simp
        omega
      rw [h1]
      rw [Set.encard]
      simp
    · -- x = 60
      have h1 : {i | (i = 1 ∧ 3 ∣ (60 : ℕ)) ∨ (i = 2 ∧ 5 ∣ (60 : ℕ)) ∨ (i = 3 ∧ 9 ∣ (60 : ℕ)) ∨
        (i = 4 ∧ 15 ∣ (60 : ℕ)) ∨ (i = 5 ∧ 25 ∣ (60 : ℕ)) ∨ (i = 6 ∧ 45 ∣ (60 : ℕ))} = {1, 2, 4} := by
        ext i
        simp
        omega
      rw [h1]
      rw [Set.encard]
      simp