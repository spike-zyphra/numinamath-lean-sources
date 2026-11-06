import Mathlib

theorem number_theory_12083 : IsLeast {n : ℕ | ∃ A B : ℕ, A ∈ Set.Icc 1 9 ∧ B ∈ Set.Icc 1 9 ∧
    A ≠ B ∧ Nat.ofDigits 10 [B, A] = (9⁻¹ : ℚ) * Nat.ofDigits 10 [B, A, A] ∧
    n = Nat.ofDigits 10 [B, A, A]} 225 := by
  constructor
  · -- Show that 225 is achievable, with A=2, B=5
    use 2, 5
    norm_num [Nat.ofDigits, Set.mem_Icc]
    <;> native_decide
  · -- Show that 225 is the least
    intro n hn
    rcases hn with ⟨A, B, hA, hB, hne, heq, hn⟩
    by_contra h
    push_neg at h
    have h1 : A ≥ 1 := by
      have hA1 : A ∈ Set.Icc (1 : ℕ) 9 := hA
      simp at hA1 ⊢
      omega
    have h1' : A ≤ 9 := by
      have hA1 : A ∈ Set.Icc (1 : ℕ) 9 := hA
      simp at hA1 ⊢
      omega
    have h2 : B ≥ 1 := by
      have hB1 : B ∈ Set.Icc (1 : ℕ) 9 := hB
      simp at hB1 ⊢
      omega
    have h2' : B ≤ 9 := by
      have hB1 : B ∈ Set.Icc (1 : ℕ) 9 := hB
      simp at hB1 ⊢
      omega
    rw [hn] at h
    simp [Nat.ofDigits] at heq h
    interval_cases A <;> interval_cases B
    <;> norm_num [Nat.ofDigits, Set.mem_Icc] at heq hA hB hne h ⊢
    <;> all_goals omega