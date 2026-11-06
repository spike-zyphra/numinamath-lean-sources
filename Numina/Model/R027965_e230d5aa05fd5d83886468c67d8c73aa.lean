import Mathlib

def a (n : ℕ) := n * (n + 1) / 2

def b (n : ℕ) := ∑ i in Finset.Icc 1 n, a i

theorem number_theory_84670 : ¬∃ n, b n = 2017 := by
  rintro ⟨n, hn⟩
  have h1 : b n = ∑ i in Finset.Icc 1 n, a i := by
    rfl
  rw [h1] at hn
  have h2 : ∑ i in Finset.Icc 1 n, a i = 2017 := hn
  have h3 : n ≤ 22 := by
    by_contra h
    push_neg at h
    have h4 : ∑ i in Finset.Icc 1 n, a i > 2017 := by
      have h5 : n ≥ 23 := by omega
      have h6 : ∑ i in Finset.Icc 1 n, a i ≥ ∑ i in Finset.Icc 1 23, a i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · -- Show that Icc 1 23 ⊆ Icc 1 n
          intro i hi
          simp at hi ⊢
          omega
        · -- Show that ∀ i ∈ Icc 1 23, a i ≤ a i
          intro i hi
          simp
      have h7 : ∑ i in Finset.Icc 1 23, a i > 2017 := by native_decide
      linarith
    linarith
  have h4 : n ≥ 19 := by
    by_contra h
    push_neg at h
    have h5 : ∑ i in Finset.Icc 1 n, a i < 2017 := by
      have h6 : n ≤ 18 := by omega
      interval_cases n <;> native_decide
    linarith
  interval_cases n <;> try { contradiction }
  <;> try { native_decide }