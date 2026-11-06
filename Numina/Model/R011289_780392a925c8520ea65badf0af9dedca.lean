import Mathlib

theorem number_theory_233634 (a : ℕ) (ha : a ∈ Finset.Ico 1 10) :
    37 ∈ (Nat.ofDigits 10 [a, a, a]).primeFactors := by
  rw [Finset.mem_Ico] at ha
  rcases ha with ⟨ha1, ha2⟩
  have h1 : Nat.ofDigits 10 [a, a, a] = 111 * a := by
    simp [Nat.ofDigits, Nat.add_mul, Nat.mul_add, add_assoc]
    <;> ring
  rw [h1]
  interval_cases a <;> native_decide