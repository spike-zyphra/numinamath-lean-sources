import Mathlib

theorem number_theory_38879 :
    Set.ncard {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ 11 ∣ (p.1 : ℤ) - p.2 ∧ p.1 ∈ (Nat.divisors (6^8)) ∧ p.2 ∈ (Nat.divisors (6^8))} = 665 := by
  have h1 : {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ 11 ∣ (p.1 : ℤ) - p.2 ∧ p.1 ∈ (Nat.divisors (6^8)) ∧ p.2 ∈ (Nat.divisors (6^8))} = Finset.filter (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0 ∧ 11 ∣ (p.1 : ℤ) - p.2) ((Nat.divisors (6^8)) ×ˢ (Nat.divisors (6^8))) := by
    ext ⟨a, b⟩
    simp
    <;> tauto
  rw [h1] at *
  rw [Set.ncard_coe_Finset]
  native_decide