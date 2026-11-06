import Mathlib

theorem algebra_115502 {u : ℕ → ℝ} (hu : u 1 > 0) (hun : ∀ n ≥ 1, u (n + 1) = -1 / (u n + 1)) :
    u 16 = u 1 := by 
  have u2 : u 2 = -1 / (u 1 + 1) := hun 1 (by norm_num)
  have u3 : u 3 = -1 / (u 2 + 1) := hun 2 (by norm_num)
  have u4 : u 4 = -1 / (u 3 + 1) := hun 3 (by norm_num)
  have u4_eq : u 4 = u 1 := by
    rw [u4, u3, u2]
    field_simp [(show u 1 + 1 ≠ 0 by linarith [hu]), (show u 1 ≠ 0 by linarith [hu])]
    <;> ring_nf 
    <;> nlinarith 
  have h5 : ∀ k : ℕ, u (3 * k + 1) = u 1 := by 
    intro k
    induction k with 
    | zero =>
      norm_num
    | succ k ih =>
      have eq6 : u (3 * (k + 1) + 1) = u (3 * k + 4) := by 
        simp [mul_add]
        <;> ring_nf <;> omega 
      have eq7 : u (3 * k + 2) = -1 / (u (3 * k + 1) + 1) := by 
        specialize hun (3 * k + 1) (by omega) 
        simpa using hun 
      have eq8 : u (3 * k + 3) = -1 / (u (3 * k + 2) + 1) := by 
        specialize hun (3 * k + 2) (by omega) 
        simpa using hun 
      have eq9 : u (3 * k + 4) = -1 / (u (3 * k + 3) + 1) := by 
        specialize hun (3 * k + 3) (by omega) 
        simpa using hun 
      rw [eq6] 
      rw [eq9, eq8, eq7] 
      rw [ih] 
      field_simp [(show u 1 + 1 ≠ 0 by linarith [hu]), (show u 1 ≠ 0 by linarith [hu])]
      <;> ring_nf 
      <;> nlinarith
  have eq10 : u 16 = u 1 := by
    specialize h5 5 
    norm_num at h5 ⊢
    linarith 
  exact_mod_cast eq10 
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith