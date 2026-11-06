import Mathlib

theorem algebra_178586 (p : ℕ → ℝ) (hp : p 0 = 1)
    (h : ∀ n, p (n + 1) = p n + 1 / p n) :
    ∃ n, p n ≥ 100 := by
  have h1 : p 0 = 1 := hp 
  have h2 : ∀ n : ℕ, p n > 0 := by
    intro n 
    induction n with 
    | zero => 
      rw [h1]
      norm_num 
    | succ n ih => 
      have eq1 : p (n + 1) = p n + 1 / p n := h n 
      rw [eq1] 
      have h3 : p n > 0 := ih 
      have h4 : 1 / p n > 0 := by 
        apply div_pos 
        norm_num 
        all_goals linarith 
      linarith 
  have h3 : ∀ n : ℕ, p (n + 1) > p n := by 
    intro n 
    have eq1 : p (n + 1) = p n + 1 / p n := h n 
    have h4 : p n > 0 := h2 n 
    have h5 : (1 / p n) > 0 := by 
      apply div_pos 
      norm_num 
      all_goals linarith 
    rw [eq1] 
    linarith 
  by_contra h4 
  push_neg at h4 
  have h4' : ∀ n, p n < (100 : ℝ) := by simpa using h4 
  have h7 : ∀ n : ℕ, p n < (100 : ℝ) := h4' 
  have h10 : ∀ n : ℕ, p n ≥ 1 + (n : ℝ) / (100 : ℝ) := by 
    intro n 
    induction n with 
    | zero => 
      rw [h1]
      norm_num 
    | succ n ih => 
      have eq1 : p (n + 1) = p n + 1 / p n := h n 
      have h4 : p n > 0 := h2 n 
      have h7 : p n < (100 : ℝ) := h7 n 
      have h8 : (1 / p n) ≥ (1 / (100 : ℝ)) := by 
        have h9 : p n ≤ (100 : ℝ) := by linarith 
        have h10 : p n > 0 := h4 
        have h11 : (100 : ℝ) > 0 := by norm_num 
        apply (div_le_div_iff (by linarith) (by linarith)).mpr 
        nlinarith 
      have eq2 : p (n + 1) = p n + 1 / p n := eq1 
      have eq3 : p (n + 1) ≥ p n + (1 / (100 : ℝ)) := by 
        linarith [eq2, h8] 
      have eq4 : p n ≥ 1 + (n : ℝ) / (100 : ℝ) := ih 
      have eq5 : p (n + 1) ≥ 1 + ( (n + (1 : ℝ) ) : ℝ) / (100 : ℝ) := by 
        have eq6 : ( (n + (1 : ℝ) ) : ℝ) / (100 : ℝ) = (n / (100 : ℝ) ) + (1 / (100 : ℝ)) := by 
          field_simp 
          <;> ring 
        rw [eq6] 
        linarith 
      simpa using eq5 
  have h11 : p 9900 ≥ 1 + (9900 : ℝ) / (100 : ℝ) := h10 9900 
  have h12 : p 9900 < (100 : ℝ) := h7 9900 
  norm_num at h11 h12 
  all_goals linarith