import Mathlib

theorem algebra_11461 {a : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n) (h : 3 * a 8 = 5 * a 13)
    (ha1 : a 1 > 0) :
    IsGreatest {∑ i in Finset.range n, a i | n ∈ Finset.Icc 1 20} (∑ i in Finset.range 20, a i) := by
  rcases ha with ⟨d, had⟩
  have h1 : a 8 = a 0 + 8 * d := by
    specialize had 8
    norm_num at had ⊢
    linarith
  have h2 : a 13 = a 0 + 13 * d := by
    specialize had 13
    norm_num at had ⊢
    linarith
  rw [h1] at h 
  rw [h2] at h
  have h3 : 3 * (a 0 + 8 * d) = 5 * (a 0 + 13 * d) := by 
    linarith 
  have h_eq1 : a 0 = -41 / 2 * d := by 
    linarith 
  have h4 : a 1 = a 0 + d := by 
    specialize had 1 
    norm_num at had 
    linarith 
  rw [h4] at ha1
  rw [h_eq1] at ha1
  have h5 : d < 0 := by 
    nlinarith 
  constructor 
  · -- Show that $\sum \20, a i$ in the set 
    use 20 
    all_goals 
      norm_num 
  · -- Show that $\sum \20, a i$ is the greatest 
    intro x hx
    rcases hx with ⟨n, hn, rfl⟩ 
    have hn1 : n ≥ 1 := by 
      have h7 : n ∈ Finset.Icc 1 20 := hn 
      simp at h7 ⊢ 
      omega 
    have hn2 : n ≤ 20 := by 
      have h7 : n ∈ Finset.Icc 1 20 := hn 
      simp at h7 ⊢ 
      omega
    have h6 : ∑ i in Finset.range n, a i ≤ ∑ i in Finset.range 20, a i := by
      have h_eq10 : ∀ (n : ℕ), ∑ i in Finset.range n, a i = (n : ℝ)/ 2 * ( 2 * a 0 + (n - 1 : ℝ) * d ) := by
        intro n
        induction n with 
        | zero => 
          simp 
        | succ n ih => 
          rw [Finset.sum_range_succ, ih]
          simp [had n]
          all_goals 
          ring_nf 
      have h_eq10' : ∑ i in Finset.range n, a i = (n : ℝ)/ 2 * ( 2 * a 0 + (n - 1 : ℝ) * d ) := h_eq10 n
      have h_eq11 : ∑ i in Finset.range 20, a i = (20 : ℝ)/ 2 * ( 2 * a 0 + (20 - 1 : ℝ) * d ) := h_eq10 20
      rw [h_eq10', h_eq11] 
      rw [h_eq1] 
      have h8 : (n : ℝ) ≤ (20 : ℝ) := by exact_mod_cast (show n ≤ 20 by linarith) 
      nlinarith [sq_nonneg (( (n : ℝ) - (20 : ℝ) ) ), h5]
    linarith