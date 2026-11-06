import Mathlib

theorem number_theory_12420 : IsLeast {n | ∃(A B : ℕ), A < 5 ∧ B < 7 ∧ Nat.digits 5 n = [A, A] ∧ Nat.digits 7 n = [B, B]} 24 := by
  constructor
  · -- First, we prove that 24 is in the set
    use 4, 3
    all_goals norm_num
    <;> native_decide
  · -- Now, we need to prove that 24 is the smallest.
    intro n hn
    rcases hn with ⟨A, B, hA, hB, hx1, hx2⟩
    by_contra h
    push_neg at h
    -- From hx1: Nat.digits 5 n = [A, A], we can write n = A + A * 5
    have h1 : n = 6 * A := by
      have hx1' : Nat.digits 5 n = [A, A] := hx1
      have h1 : n = A + A * 5 := by 
        rw [← Nat.ofDigits_digits 5 n]
        rw [hx1']
        simp [Nat.ofDigits, mul_add, add_mul]
        all_goals ring_nf
      linarith
    -- From hx2: Nat.digits 7 n = [B, B], we can write n = B + B * 7
    have h2 : n = 8 * B := by 
      have hx2' : Nat.digits 7 n = [B, B] := hx2
      have h5 : n = B + B * 7 := by 
        rw [← Nat.ofDigits_digits 7 n]
        rw [hx2']
        simp [Nat.ofDigits, mul_add, add_mul]
        all_goals ring_nf
      have h6 : n = 8 * B := by 
        omega
      exact h6
    have h3 : A ≤ 4 := by
      omega
    have h4 : B ≤ 6 := by
      omega
    interval_cases A <;> interval_cases B <;> norm_num [h1, h2] at h hx1 hx2 hA hB 
    <;> try { contradiction }
    <;> omega