import Mathlib

theorem number_theory_76014 (P : Set ℕ) (hP : P = {x | Nat.Prime x}) (A : Set ℕ)
    (hA : A ⊆ P) (hA1 : A.ncard ≥ 2) (hA2 : ∀ n > 0, ∀ p : Fin n → ℕ,
    (∀ i j, p i = p j → i = j) ∧ (∀ i, p i ∈ A) ∧
    (∀ x, Nat.Prime x → x ∣ ∏ i, p i - 1 → x ∈ A)) :
    A = P := by
  have h3 := hA2 1 (by norm_num) (λ _ : Fin 1 => (1 : ℕ))
  rcases h3 with ⟨h_inj, h1, h2⟩
  have h2' : ∀ x : ℕ, Nat.Prime x → x ∈ A := by
    intro x hx
    have h22 := h2 x hx
    have hdiv : x ∣ (1 - 1 : ℕ) := by
      simp 
    have hx2_in_A := h22 hdiv
    exact hx2_in_A
  have h3_eq : ∀ x : ℕ, x ∈ A ↔ Nat.Prime x := by 
    intro x 
    constructor 
    · -- Assume x ∈ A, need Nat.Prime x 
      intro h 
      have h4 : x ∈ P := hA h 
      rw [hP] at h4 
      exact h4 
    · -- Assume Nat.Prime x, need x ∈ A 
      intro h 
      apply h2' x h 
  ext x 
  simp [hP, h3_eq]