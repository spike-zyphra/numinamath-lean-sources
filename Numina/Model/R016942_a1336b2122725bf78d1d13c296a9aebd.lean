import Mathlib

theorem number_theory_205932 :
    IsLeast {q : ℕ | ∃ p : ℕ, 0 < p ∧ 0 < q ∧ (72 / 487 : ℚ) < (p / q : ℚ) ∧ (p / q : ℚ) < (18 / 121 : ℚ)} 27 := by
  constructor
  · -- Show (4, 27) is in the set
    use 4
    norm_num
  · -- Show that 27 is the smallest
    intro q h
    rcases h with ⟨p, hp, hq, h1, h2⟩
    by_contra h'
    push_neg at h'
    have h1' : (72 : ℚ) / (487 : ℚ) < (p : ℚ) / (q : ℚ) := h1
    have h2' : (p : ℚ) / (q : ℚ) < (18 : ℚ) / (121 : ℚ) := h2
    have h5 : 72 * (q : ℚ) < 487 * (p : ℚ) := by
      have h5 : (72 : ℚ) / (487 : ℚ) < (p : ℚ) / (q : ℚ) := h1
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h5
      linarith
    have h6 : 121 * (p : ℚ) < 18 * (q : ℚ) := by
      have h6 : (p : ℚ) / (q : ℚ) < (18 : ℚ) / (121 : ℚ) := h2
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h6
      linarith
    have h7 : 72 * q < 487 * p := by
      exact_mod_cast h5
    have h8 : 121 * p < 18 * q := by
      exact_mod_cast h6
    have h9 : q ≤ 26 := by
      omega
    interval_cases q <;> try { 
      omega -- solve contradiction for p
    } <;> try { contradiction }