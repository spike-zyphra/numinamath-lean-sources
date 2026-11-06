import Mathlib

theorem number_theory_219503 (n : ℕ) (hn : n ≠ 0) (h : ⌊(⌊(91 / n : ℝ)⌋ / n : ℝ)⌋ = 1) :
    n = 7 ∨ n = 8 ∨ n = 9 := by
  have h1 : n ≤ 9 := by
    by_contra h1
    push_neg at h1
    have h2 : n ≥ 10 := by omega
    have h3 : (91 / n : ℝ) ≤ 9.1 := by
      have h5 : n ≥ 10 := h2
      have h8 : (n : ℝ) ≥ (10 : ℝ) := by
        have h9 : n ≥ 10 := h5
        have h10 : (n : ℝ) ≥ (10 : ℝ) := by
          exact_mod_cast h9
        linarith
      have h11 : (91 : ℝ) / (n : ℝ) ≤ (9.1 : ℝ) := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith
      linarith
    have h4 : ⌊(91 / n : ℝ)⌋ ≤ 9 := by
      have h5 : (91 / n : ℝ) ≤ 9.1 := h3
      by_contra h7
      push_neg at h7
      have h8 : ⌊(91 / n : ℝ)⌋ ≥ 10 := by omega
      have h11 : (⌊(91 / n : ℝ)⌋ : ℝ) ≥ (10 : ℝ) := by exact_mod_cast h8
      have h12 : (⌊(91 / n : ℝ)⌋ : ℝ) ≤ (91 / n : ℝ) := by exact_mod_cast (Int.floor_le (91 / n : ℝ))
      nlinarith
    have h11 : (⌊(91 / n : ℝ)⌋ : ℝ) ≤ (9 : ℝ) := by exact_mod_cast h4
    have h13 : (⌊(91 / n : ℝ)⌋ / n : ℝ) < (1 : ℝ) := by
      have h14 : (n : ℝ) ≥ (10 : ℝ) := by
        have h5 : n ≥ 10 := h2
        have h6 : (n : ℝ) ≥ (10 : ℝ) := by exact_mod_cast h5
        linarith
      have h17 : (⌊(91 / n : ℝ)⌋ / n : ℝ) ≤ (9 / n : ℝ) := by
        apply (div_le_div_right (by positivity)).mpr
        nlinarith
      have h18 : (9 / n : ℝ) ≤ (9 / 10 : ℝ) := by
        have h19 : (n : ℝ) ≥ (10 : ℝ) := h14
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith
      have h19 : (⌊(91 / n : ℝ)⌋ / n : ℝ) ≤ (9 / 10 : ℝ) := by
        linarith
      have h22 : (9 / 10 : ℝ) < (1 : ℝ) := by norm_num
      nlinarith
    have h14 : ⌊(⌊(91 / n : ℝ)⌋ / n : ℝ)⌋ = 0 := by
      have h11 : (⌊(91 / n : ℝ)⌋ / n : ℝ) < (1 : ℝ) := h13
      have h12 : (⌊(91 / n : ℝ)⌋ / n : ℝ) ≥ 0 := by positivity
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> nlinarith
    omega
  interval_cases n <;> norm_num at h ⊢ <;> tauto