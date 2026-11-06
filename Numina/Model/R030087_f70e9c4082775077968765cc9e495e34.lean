import Mathlib

theorem algebra_106543 :
    Set.ncard {p : ℕ × ℕ | p.1 ≤ 10 ∧ p.2 ≤ 10 ∧ 1 / 4 < (p.2 / p.1 : ℝ) ∧ (p.2 / p.1 : ℝ) < 1 / 3} = 2 := by
  have h1 : {p : ℕ × ℕ | p.1 ≤ 10 ∧ p.2 ≤ 10 ∧ 1 / 4 < (p.2 / p.1 : ℝ) ∧ (p.2 / p.1 : ℝ) < 1 / 3} = {(7, 2), (10, 3)} := by
    ext ⟨a, b⟩
    simp
    constructor
    · -- Assume ⟨a, b⟩ is in the original set, prove ⟨a, b⟩ ∈ {(7, 2), (10, 3)}
      rintro ⟨ha, hb, h1, h2⟩
      have h3 : a > 0 := by
        by_contra h
        push_neg at h
        have ha0 : a = 0 := by linarith
        rw [ha0] at h1
        norm_num at h1
      have h4 : (3 * (b : ℝ) < (a : ℝ)) := by
        have h5 : (b / (a : ℝ) < 1 / 3) := by linarith
        have h7 : (a : ℝ) > 0 := by exact_mod_cast (show (0 : ℕ) < a by linarith)
        have h8 : 3 * (b : ℝ) < (a : ℝ) := by
          have h9 : b / (a : ℝ) < 1 / 3 := h5
          have h12 : (a : ℝ) > 0 := by positivity
          have h10 : (b : ℝ) < (a : ℝ) / 3 := by 
            rw [div_lt_iff'] at h9 
            all_goals norm_num at h9 ⊢
            all_goals nlinarith
          nlinarith
        linarith
      have h5 : (a : ℝ) < 4 * (b : ℝ) := by
        have h4 : (1 / 4 < (b / (a : ℝ))) := by linarith
        have h7 : (a : ℝ) > 0 := by exact_mod_cast (show (0 : ℕ) < a by linarith)
        have h6 : (a : ℝ) < 4 * (b : ℝ) := by
          have h4' : (1 / 4 < b / (a : ℝ)) := h4
          have : (a : ℝ) < 4 * (b : ℝ) := by 
            rw [lt_div_iff'] at h4'
            all_goals norm_num at h4' ⊢
            all_goals nlinarith
          linarith
        linarith
      have h4' : 3 * b < a := by
        have h4' : (3 * (b : ℝ) < (a : ℝ)) := h4
        norm_cast at h4' ⊢
      have h5' : a < 4 * b := by
        have h5' : (a : ℝ) < 4 * (b : ℝ) := h5
        norm_cast at h5' ⊢
      interval_cases a <;> interval_cases b <;> norm_num at h4' h5' ha hb h1 h2 ⊢ <;> tauto
    · -- Assume ⟨a, b⟩ ∈ {(7, 2), (10, 3)}, prove ⟨a, b⟩ is in the original set
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (7, 2)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check (10, 3)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_pair]
  all_goals norm_num