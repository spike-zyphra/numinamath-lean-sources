import Mathlib

theorem number_theory_290035 {n m : ℕ} (hn : IsGreatest {x | 0 < x ∧ x^2 < 2018} n)
    (hm : IsLeast {x | 0 < x ∧ 2018 < x^2} m) :
    m^2 - n^2 = 89 := by
  have h1 : n ∈ {x | 0 < x ∧ x^2 < 2018} := hn.left
  have h2 : ∀ x, x ∈ {x | 0 < x ∧ x^2 < 2018} → x ≤ n := hn.right
  have hn1 : 0 < n := by 
    have h := h1.left
    linarith
  have hn2 : n ^ 2 < 2018 := by
    have h := h1.right
    linarith
  have hn3 : n ≥ 44 := by
    have h3 := h2 44 (by constructor <;> norm_num)
    linarith
  have hn4 : n ≤ 44 := by
    by_contra h
    push_neg at h
    have h5 : n ^ 2 ≥ 2025 := by
      have : n ≥ 45 := by linarith
      have h6 : n ^ 2 ≥ 45 ^ 2 := by
        apply Nat.pow_le_pow_left
        all_goals linarith
      norm_num at h6 ⊢
      linarith
    linarith
  have hn5 : n = 44 := by 
    linarith
  have hm1 : m ∈ {x | 0 < x ∧ 2018 < x^2} := hm.left
  have hm2 : ∀ x, x ∈ {x | 0 < x ∧ 2018 < x^2} → m ≤ x := hm.right
  have hm11 : 0 < m := by
    have h := hm1.left
    linarith
  have hm12 : 2018 < m ^ 2 := by
    have h := hm1.right
    linarith
  have hm3 : m ≥ 45 := by
    by_contra h
    push_neg at h
    have : m ≤ 44 := by linarith
    have : m ^ 2 ≤ 44 ^ 2 := by
      apply Nat.pow_le_pow_left
      all_goals linarith
    nlinarith
  have hm4 : m ≤ 45 := by
    have h3 := hm2 45 (by constructor <;> norm_num)
    linarith
  have hm5 : m = 45 := by 
    linarith
  calc
    m ^ 2 - n ^ 2 = 45 ^ 2 - 44 ^ 2 := by rw [hm5, hn5]
    _ = 2025 - 1936 := by norm_num
    _ = 89 := by norm_num