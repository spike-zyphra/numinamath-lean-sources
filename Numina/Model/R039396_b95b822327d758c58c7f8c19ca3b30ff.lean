import Mathlib

theorem algebra_263032 {a d : ℤ} (h₀ : a + d ≠ 0) (h₁ : ∑ i ∈ Finset.range 3, (a + d * i) = 327)
    (h₂ : ∑ i ∈ Finset.range 57, (a + d * i) = 57) :
    IsGreatest {∑ i ∈ Finset.range n, (a + d * i) | n} 1653 := by
  have h3 : a + d = 109 := by 
    simp [Finset.sum_range_succ] at h₁ 
    linarith 
  have h4 : a + 28 * d = 1 := by 
    simp [Finset.sum_range_succ] at h₂ 
    ring_nf at h₂ 
    linarith 
  have h5 : d = -4 := by 
    linarith [h3, h4] 
  have h6 : a = 113 := by 
    linarith [h3, h5] 
  constructor
  · -- Show 1653 in the set 
    use 29 
    rw [h6, h5] 
    norm_num [Finset.sum_range_succ] 
  · -- Show that for all n, sum <= 1653 
    intro s 
    rintro ⟨n, hn⟩ 
    rw [h6, h5] at hn
    have h7 : (∑ i in Finset.range n, ((113 : ℤ) + (-4 : ℤ) * i)) ≤ 1653 := by 
      have h8 : ∀ n : ℕ, (∑ i in Finset.range n, ((113 : ℤ) + (-4 : ℤ) * i)) ≤ 1653 := by 
        intro n 
        have h9 : ∀ (n : ℕ), (∑ i in Finset.range n, ((113 : ℤ) + (-4 : ℤ) * i)) = (115 * (n : ℤ) - 2 * (n : ℤ) ^ 2) := by 
          intro n 
          induction n with 
          | zero => 
            simp 
          | succ n ih => 
            rw [Finset.sum_range_succ, ih] 
            simp 
            <;> ring 
        have h9_n := h9 n 
        rw [h9_n] 
        by_cases h : (n : ℤ) ≤ 28 
        · 
          nlinarith [sq_nonneg ((n : ℤ) - 28 : ℤ), sq_nonneg ((n : ℤ) - 29 : ℤ)]
        · 
          nlinarith [sq_nonneg ((n : ℤ) - 28 : ℤ), sq_nonneg ((n : ℤ) - 29 : ℤ)]
      specialize h8 n 
      linarith 
    linarith [h7, hn]