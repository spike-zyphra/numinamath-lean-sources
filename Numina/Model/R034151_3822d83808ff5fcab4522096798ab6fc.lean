import Mathlib

open Real

theorem inequalities_168045 {b : ℝ} (hb : 0 < b) (n : ℕ) (hn : n > 2)
    (d : ℝ) (hd : d = ((⌊b⌋ + 1 - b) * ⌊b⌋) / (⌊b⌋ + 1)) :
    (d + n - 2) / (⌊b⌋ + n - 2) > (⌊b⌋ + n - 1 - b) / (⌊b⌋ + n - 1) := by
  have h1 : ⌊b⌋ ≥ 0 := by
    have h2 : (b : ℝ) > (0 : ℝ) := hb
    have h3 : ⌊b⌋ ≥ 0 := by
      by_contra h
      push_neg at h
      have h4 : ⌊b⌋ ≤ -1 := by omega
      have h5 : (⌊b⌋ : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h4
      have h6 : b < (0 : ℝ) := by
        have h7 : b < (⌊b⌋ + 1 : ℝ) := by exact_mod_cast Int.lt_floor_add_one b
        nlinarith
      linarith
    exact h3
  have h2 : ⌊b⌋ + n - 2 > 0 := by
    have hn' : (n : ℝ) > (2 : ℝ) := by
      have hn1 : n > 2 := hn
      have hn2 : n ≥ 3 := by omega
      have hn3 : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast hn2
      nlinarith
    have h4 : (⌊b⌋ : ℝ) ≥ (0 : ℝ) := by exact_mod_cast h1
    have h5 : (⌊b⌋ : ℝ) + (n : ℝ) - 2 > (0 : ℝ) := by
      have hn' : (n : ℝ) > (2 : ℝ) := by
        have hn1 : n > 2 := hn
        have hn2 : n ≥ 3 := by omega
        have hn3 : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast hn2
        nlinarith
      nlinarith
    exact_mod_cast h5
  have h3 : ⌊b⌋ + n - 1 > 0 := by
    have hn' : (n : ℝ) > (2 : ℝ) := by
      have hn1 : n > 2 := hn
      have hn2 : n ≥ 3 := by omega
      have hn3 : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast hn2
      nlinarith
    have h4 : (⌊b⌋ : ℝ) ≥ (0 : ℝ) := by exact_mod_cast h1
    have h5 : (⌊b⌋ : ℝ) + (n : ℝ) - 1 > (0 : ℝ) := by
      have hn' : (n : ℝ) > (2 : ℝ) := by
        have hn1 : n > 2 := hn
        have hn2 : n ≥ 3 := by omega
        have hn3 : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast hn2
        nlinarith
      nlinarith
    exact_mod_cast h5
  have h4 : (⌊b⌋ + n - 2 : ℝ) > 0 := by
    exact_mod_cast h2
  have h5 : (⌊b⌋ + n - 1 : ℝ) > 0 := by
    exact_mod_cast h3
  have h7 : (d + (n : ℝ) - 2) * (⌊b⌋ + (n : ℝ) - 1) > (⌊b⌋ + (n : ℝ) - 1 - b) * (⌊b⌋ + (n : ℝ) - 2) := by
    rw [hd]
    have h11 : (⌊b⌋ : ℝ) ≥ (0 : ℝ) := by exact_mod_cast h1
    have h12 : (⌊b⌋ + 1 : ℝ) > 0 := by
      have h11' : (⌊b⌋ : ℝ) ≥ (0 : ℝ) := h11
      nlinarith
    have h13 : (( (⌊b⌋ + 1 - b) * ⌊b⌋ ) / (⌊b⌋ + 1) + (n : ℝ) - 2) * (⌊b⌋ + (n : ℝ) - 1) - (⌊b⌋ + (n : ℝ) - 1 - b) * (⌊b⌋ + (n : ℝ) - 2) > 0 := by
      have h14 : (( (⌊b⌋ + 1 - b) * ⌊b⌋ ) / (⌊b⌋ + 1) + (n : ℝ) - 2) * (⌊b⌋ + (n : ℝ) - 1) - (⌊b⌋ + (n : ℝ) - 1 - b) * (⌊b⌋ + (n : ℝ) - 2) = 
        ( (⌊b⌋ + 1 - b) * ⌊b⌋ * (⌊b⌋ + (n : ℝ) - 1) + ((n : ℝ) - 2) * (⌊b⌋ + (n : ℝ) - 1) * (⌊b⌋ + 1) - (⌊b⌋ + (n : ℝ) - 1 - b) * (⌊b⌋ + (n : ℝ) - 2) * (⌊b⌋ + 1) ) / (⌊b⌋ + 1) := by
        field_simp
        <;> ring
      rw [h14]
      have h14' : (⌊b⌋ + 1 - b) * ⌊b⌋ * (⌊b⌋ + (n : ℝ) - 1) + ((n : ℝ) - 2) * (⌊b⌋ + (n : ℝ) - 1) * (⌊b⌋ + 1) - (⌊b⌋ + (n : ℝ) - 1 - b) * (⌊b⌋ + (n : ℝ) - 2) * (⌊b⌋ + 1) > (0 : ℝ) := by
        have h7 : (⌊b⌋ : ℝ) ≥ (0 : ℝ) := h11
        have h8 : (b : ℝ) > (0 : ℝ) := hb
        have h9 : (⌊b⌋ + 1 : ℝ) > (0 : ℝ) := h12
        have hn1 : (n : ℝ) > (2 : ℝ) := by
          have hn2 : n > 2 := hn
          have hn3 : n ≥ 3 := by omega
          have hn4 : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast hn3
          nlinarith
        nlinarith [sq_nonneg ((b - ⌊b⌋ : ℝ) - 1), sq_nonneg ((⌊b⌋ : ℝ) + 1), sq_nonneg ((n : ℝ) - 2), sq_nonneg ((⌊b⌋ : ℝ) - (⌊b⌋ : ℝ) + 1), mul_pos hb (show (0 : ℝ) < (⌊b⌋ + 1 : ℝ) by linarith), 
          sq_nonneg ((⌊b⌋ + 1 : ℝ) - (⌊b⌋ : ℝ)), sq_nonneg ((⌊b⌋ : ℝ) - (⌊b⌋ : ℝ) + 1 - b), mul_pos (show (0 : ℝ) < (⌊b⌋ + 1 : ℝ) by linarith) (show (0 : ℝ) < (n : ℝ) - 2 by linarith)
        ]
      apply div_pos
      . linarith
      all_goals linarith
    linarith
  have h6 : (d + (n : ℝ) - 2) / (⌊b⌋ + (n : ℝ) - 2) > (⌊b⌋ + (n : ℝ) - 1 - b) / (⌊b⌋ + (n : ℝ) - 1) := by
    have h7' : (d + (n : ℝ) - 2) * (⌊b⌋ + (n : ℝ) - 1) > (⌊b⌋ + (n : ℝ) - 1 - b) * (⌊b⌋ + (n : ℝ) - 2) := h7
    have h8 : (⌊b⌋ + (n : ℝ) - 2) > 0 := h4
    have h9 : (⌊b⌋ + (n : ℝ) - 1) > 0 := h5
    apply (div_lt_div_iff (by linarith) (by linarith)).mpr
    linarith
  exact_mod_cast h6