import Mathlib

theorem number_theory_31025 (A : Finset ℤ) (hA : A.card = 65)
    (hA' : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → x % 2016 ≠ y % 2016) :
    ∃ a b c d, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ d ∈ A ∧ 2016 ∣ a + b - c - d := by
  have h1 : A.card = 65 := hA
  have h2 : A.card = 65 := hA
  have h3 : A.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    by_contra h
    rw [h] at h2
    simp at h2

  rcases h3 with ⟨a, ha⟩
  exact ⟨a, a, a, a, by simp [ha], by simp [ha], by simp [ha], by simp [ha], by simp⟩