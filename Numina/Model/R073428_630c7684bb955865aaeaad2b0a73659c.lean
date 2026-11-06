import Mathlib

theorem algebra_285511 (a S : ℕ → ℝ) (hS : S = fun n => ∑ i in Finset.range n, a i)
    (hS15 : S 15 = 30) (ha : ∃ d, ∀ n, a n = a 0 + d * n) :
    a 0 + a 7 + a 14 = 6 := by
  rcases ha with ⟨d, hd⟩
  have hS15_def : S 15 = 15 * a 0 + 105 * d := by
    rw [hS]
    simp [Finset.sum_range_succ, hd 1, hd 2, hd 3, hd 4, hd 5, hd 6, hd 7, hd 8, hd 9, hd 10, hd 11, hd 12, hd 13, hd 14]
    ring_nf
    <;> simp [hd]
  have eq1 : 15 * a 0 + 105 * d = 30 := by 
    rw [hS15_def] at hS15
    linarith
  have eq2 : a 0 + 7 * d = 2 := by
    linarith 
  have h1 : a 7 = a 0 + 7 * d := by 
    specialize hd 7
    rw [hd]
    ring_nf
  have h2 : a 14 = a 0 + 14 * d := by
    specialize hd 14
    rw [hd]
    ring_nf
  have h3 : a 0 + a 7 + a 14 = 3 * (a 0 + 7 * d) := by
    rw [h1, h2]
    linarith 
    <;> ring_nf <;> linarith 
  rw [h3, eq2]
  norm_num 
  <;> linarith