import Mathlib

theorem number_theory_12724 (M : Finset ℕ) (hM : M = {1, 3, 5, 7, 9}) (A : Finset ℕ)
    (hA : A.Nonempty) (hA1 : ∀ x ∈ A, x + 4 ∈ M) (hA2 : ∀ x ∈ A, x - 4 ∈ M) :
    A = {5} := by
  have h5 : 5 ∈ A := by
    have hne : A.Nonempty := hA
    rcases hne with ⟨a, ha⟩
    have h1 : a + 4 ∈ M := hA1 a ha
    have h2 : a - 4 ∈ M := hA2 a ha
    rw [hM] at h1 h2
    simp [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    have ha5 : a = 5 := by
      omega
    have h6 : 5 ∈ A := by
      have ha' : a ∈ A := ha
      rw [ha5] at ha'
      tauto
    assumption
  ext x
  simp
  constructor
  · -- Assume x ∈ A, need to show x = 5
    intro hx
    have hx1 : x + 4 ∈ M := hA1 x hx
    have hx2 : x - 4 ∈ M := hA2 x hx
    rw [hM] at hx1 hx2
    simp [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
    omega
  · -- Assume x = 5, need to show x ∈ A
    intro hx
    rw [hx]
    exact h5