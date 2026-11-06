import Mathlib

def S : ℕ → ℝ
| n => ∑ i in Finset.Icc 1 n, i

theorem algebra_599766 {f : ℕ → ℝ} (hf : ∀ n, f n = S n / ((n + 32) * S (n + 1))) :
    IsGreatest (Set.image f {n | ∃ m, n = m}) (1 / 50) := by 
  have h1 : ∀ n, f n = S n / ((n + 32) * S (n + 1)) := hf
  have h2 : 1 / 50 ∈ Set.image f {n | ∃ m, n = m} := by 
    use 8 
    constructor 
    · -- Show that 8 is in the domain {n | ∃ m, n = m}
      use 8 
    · -- Show that f 8 = 1 / 50 
      rw [h1 8]
      have h3 : S 8 = (36 : ℝ) := by
        simp [S]
        norm_num [Finset.sum_Icc_succ_top]
      have h4 : S 9 = (45 : ℝ) := by 
        simp [S]
        norm_num [Finset.sum_Icc_succ_top]
      simp [h3, h4]
      all_goals norm_num
  constructor 
  · -- Show that 1/50 is in the image 
    exact h2
  · -- Show that 1/50 is the greatest element in the image 
    intro y hy 
    rcases hy with ⟨n, hn⟩
    have h5 : f n = y := by
      linarith 
    by_cases h8 : n = 0 
    · -- Case where n = 0 
      rw [h8] at h5 
      simp [h1, S] at h5 
      linarith 
    · -- Assume n ≠ 0 
      have h9 : n ≥ 1 := by 
        by_contra h9 
        push_neg at h9 
        have h0 : n = 0 := by linarith 
        tauto 
      have h6 : ∀ k : ℕ, S k = (↑k * (↑k + 1) / 2 : ℝ) := by
        intro k 
        rw [S]
        induction k with 
        | zero =>
          simp 
        | succ k ih =>
          rw [Finset.sum_Icc_succ_top (by linarith)]
          rw [ih]
          field_simp at *
          ring_nf 
      have h10 : f n = (↑n : ℝ) / ((↑n + 32) * (↑n + 2) : ℝ) := by 
        rw [h1 n]
        have hS1 : S n = (↑n * (↑n + 1) / 2 : ℝ) := h6 n
        have hS2 : S (n + 1) = ((↑n + 1) * (↑n + 2) / 2 : ℝ) := by 
          have hS2 := h6 (n + 1)
          simp [show (↑(n + 1 : ℕ) : ℝ) = (↑n + 1 : ℝ) by simp] at hS2 ⊢ 
          all_goals linarith 
        rw [hS1, hS2] 
        field_simp 
        <;> ring 
      have h11 : (↑n : ℝ) / ((↑n + 32) * (↑n + 2) : ℝ) ≤ (1 / 50 : ℝ) := by 
        have h12 : (↑n : ℝ) * 50 ≤ (↑n + 32) * (↑n + 2) := by 
          nlinarith [sq_nonneg ((↑n : ℝ) - 8)]
        have h13 : (↑n / ((↑n + 32) * (↑n + 2)) : ℝ) ≤ (1 / 50 : ℝ) := by 
          apply (div_le_div_iff (by positivity) (by positivity)).mpr 
          nlinarith 
        exact h13 
      linarith [h5, h10, h11]