import Mathlib

theorem number_theory_242997 :
    IsLeast {p : ℕ | ∃ q : ℕ, p > 0 ∧ q > 0 ∧ (5 / 8 : ℚ) < p / q ∧ p / q < (7 / 8 : ℚ) ∧ p + q = 2005} 772 := by
  constructor
  · -- Show that 772 is in the set
    use 1233
    norm_num
  · -- We need to show that for any p in the set, 772 ≤ p
    intro p hp
    rcases hp with ⟨q, hp_pos, hq_pos, h1, h2, heq⟩
    by_contra h
    push_neg at h
    -- Assume p < 772, then p ≤ 771
    have h3 : p ≤ 771 := by
      omega
    -- Now we show that p ≤ 771 leads to a contradiction
    have h4 : (p : ℚ) ≤ (771 : ℚ) := by
      exact_mod_cast h3
    have h5 : (q : ℚ) = (2005 : ℚ) - (p : ℚ) := by
      have h6 : (p : ℚ) + (q : ℚ) = (2005 : ℚ) := by
        exact_mod_cast heq
      linarith
    -- Show that $\frac{5}{8} \geq \frac{p}{q}$
    have h7 : (5 / 8 : ℚ) ≥ (p / q : ℚ) := by
      have h8 : (5 : ℚ) * (q : ℚ) ≥ 8 * (p : ℚ) := by
        rw [h5] at *
        have h9 : (p : ℚ) ≤ (771 : ℚ) := by
          exact_mod_cast h3
        nlinarith
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    -- Contradicts with $\frac{5}{8} < \frac{p}{q}$
    linarith