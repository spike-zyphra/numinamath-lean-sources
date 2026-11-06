import Mathlib


lemma lemma_1 (n : ℕ) (a : ℕ → ℝ) (h : ∃ d, ∀ k, a k = a 0 + d * k)
    (Sodd Seven : ℝ) (hSodd : Sodd = ∑ i in Finset.range (n + 1), a (2 * i + 1))
    (hSeven : Seven = ∑ i in Finset.range n, a (2 * i + 2)) (hn : n > 0) :
    n * Sodd = (n + 1) * Seven := by
  rcases h with ⟨d, had⟩
  have h1 : Sodd = ∑ i in Finset.range (n + 1), a (2 * i + 1) := by
    linarith [hSodd]
  have h2 : Seven = ∑ i in Finset.range n, a (2 * i + 2) := by
    linarith [hSeven]
  rw [h1, h2]
  have h3 : ∀ i : ℕ, a (2 * i + 1) = a 0 + d * (2 * i + 1 : ℝ) := by
    intro i
    specialize had (2 * i + 1)
    simpa using had
  have h4 : ∀ i : ℕ, a (2 * i + 2) = a 0 + d * (2 * i + 2 : ℝ) := by
    intro i
    specialize had (2 * i + 2)
    simpa using had
  have h5 : ∑ i in Finset.range (n + 1), a (2 * i + 1) = (n + 1 : ℝ) * a 0 + d * ((n + 1 : ℝ) ^ 2) := by
    have h5a : ∀ (n : ℕ), ∑ i in Finset.range (n + 1), a (2 * i + 1) = (n + 1 : ℝ) * a 0 + d * ((n + 1 : ℝ) ^ 2) := by
      intro n
      induction n with
      | zero =>
        norm_num [Finset.sum_range_succ, h3]
        <;> ring_nf
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp [h3]
        ring_nf
    specialize h5a n
    linarith
  have h6 : ∑ i in Finset.range n, a (2 * i + 2) = (n : ℝ) * a 0 + d * ((n : ℝ) * (n + 1 : ℝ)) := by
    have h6a : ∀ (n : ℕ), ∑ i in Finset.range n, a (2 * i + 2) = (n : ℝ) * a 0 + d * ((n : ℝ) * (n + 1 : ℝ)) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp [h4]
        ring_nf
    specialize h6a n
    linarith
  rw [h5, h6]
  simp [mul_add, mul_assoc]
  <;> ring_nf


theorem algebra_322232 {n : ℕ} (hn : n > 0) (a : ℕ → ℝ)
    (h : ∃ d, ∀ k, a k = a 0 + d * k) (hodd : ∑ i in Finset.range (n + 1), a (2 * i + 1) = 310)
    (heven : ∑ i in Finset.range n, a (2 * i + 2) = 300) :
    n = 30 := by 
  have h1 : (n : ℝ) * (∑ i in Finset.range (n + 1), a (2 * i + 1)) = (↑n + 1) * (∑ i in Finset.range n, a (2 * i + 2)) := by
    have h2 := lemma_1 n a h (∑ i in Finset.range (n + 1), a (2 * i + 1)) (∑ i in Finset.range n, a (2 * i + 2)) (by linarith) (by linarith) hn
    linarith
  have eq1 : (n : ℝ) * (310 : ℝ) = (↑n + 1) * (300 : ℝ) := by
    rw [show (∑ i in Finset.range (n + 1), a (2 * i + 1) : ℝ) = 310 by linarith [hodd]] at h1
    rw [show (∑ i in Finset.range n, a (2 * i + 2) : ℝ) = 300 by nlinarith [heven]] at h1
    linarith
  have eq2 : (n : ℝ) = (30 : ℝ) := by
    nlinarith
  have eq3 : n = 30 := by
    have eq5 : (n : ℝ) = (30 : ℝ) := eq2
    exact_mod_cast eq5
  exact_mod_cast eq3