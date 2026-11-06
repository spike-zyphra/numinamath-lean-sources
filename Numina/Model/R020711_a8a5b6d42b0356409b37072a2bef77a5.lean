import Mathlib

theorem number_theory_275633 :
    (∀ n : ℕ, ¬(2 ∣ n) ∧ ¬(3 ∣ n) → ∃ k : ℕ, n = 6 * k + 1 ∨ n = 6 * k + 5) ∧
    (∀ m : ℕ, ∃ k : ℕ, m = 6 * k + 1 ∨ m = 6 * k + 5 →
      ∃ l : ℕ, m * (6 * l + 1) = 6 * (l + k) + 1) ∧
    (∀ n : ℕ, ∃ k : ℕ, n = 6 * k + 1 ∨ n = 6 * k + 5 →
      ∃ l : ℕ, n * (6 * l + 5) = 6 * (l + k) + 5) := by
  constructor
  · -- First part: prove that every number not divisible by 2 and 3 is of the form 6k+1 or 6k+5
    intro n hn
    rcases hn with ⟨h2, h3⟩
    have h1 : n % 2 = 1 := by
      omega
    have h2' : n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    have h3' : n % 6 = 1 ∨ n % 6 = 5 := by
      omega
    rcases h3' with (h | h)
    · -- Case n % 6 = 1
      refine ⟨n / 6, Or.inl ?_⟩
      omega
    · -- Case n % 6 = 5
      refine ⟨n / 6, Or.inr ?_⟩
      omega
  constructor
  · -- Second part
    intro m
    use m
    intro h
    use 0
    simp [h]
    <;> ring_nf
    <;> omega
  · -- Third part
    intro n
    use n
    intro h
    use 0
    simp [h]
    <;> ring_nf
    <;> omega