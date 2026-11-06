
import Mathlib

/- r and s are integers that $3r ≥ 2s - 3$ and $4s ≥ 4 + 12$. Whta is the smallest possible value of r/s ? -/
theorem inequalities_188771 (r s : ℤ) (h₀ : 3 * r ≥ 2 * s - 3) (h₁ : 4 * s ≥ r + 12) :
    IsLeast {x : ℝ | ∃ r s : ℤ, 3 * r ≥ 2 * s - 3 ∧ 4 * s ≥ r + 12 ∧ x = r / s} (1 / 2) := by
  constructor
  · -- Let's prove that 1/2 is attainable
    use 2, 4
    norm_num
  · -- Now, we need to prove that 1/2 is a lower bound for all elements in the set
    intro x hx
    rcases hx with ⟨r, s, h₀, h₁, hx⟩
    have h2 : (r : ℝ) / s ≥ (1 : ℝ) / 2 := by
      have h_s_pos : (s : ℝ) > 0 := by
        by_contra h
        push_neg at h
        have h_s_nonpos : (s : ℝ) ≤ 0 := by linarith
        have h_s_int : s ≤ 0 := by
          exact_mod_cast h_s_nonpos
        by_cases h_s_eq_zero : s = 0
        · -- s = 0 leads to a contradiction
          rw [h_s_eq_zero] at h₁
          omega
        · -- s < 0 leads to a contradiction
          have h_s_neg : s < 0 := by omega
          have h3 : r ≤ 4 * s - 12 := by linarith
          have h4 : 3 * r ≥ 2 * s - 3 := h₀
          have h5 : s ≥ 4 := by
            by_contra h6
            push_neg at h6
            have h7 : s ≤ 3 := by omega
            omega
          linarith
      have h3 : (r : ℝ) ≥ (1 : ℝ) / 2 * (s : ℝ) := by
        by_contra h
        push_neg at h
        have h4 : (s : ℝ) > 0 := h_s_pos
        have h5 : 2 * (r : ℝ) < (s : ℝ) := by linarith
        have h6 : 2 * r < s := by
          by_contra h7
          push_neg at h7
          have h8 : (2 * r : ℝ) ≥ (s : ℝ) := by
            exact_mod_cast h7
          linarith
        omega
      have h4 : (s : ℝ) > 0 := h_s_pos
      have h5 : (r : ℝ) ≥ (1 : ℝ) / 2 * (s : ℝ) := h3
      have h6 : (r : ℝ) / s ≥ (1 : ℝ) / 2 := by
        have h7 : (s : ℝ) > 0 := h4
        have h8 : (r : ℝ) ≥ (1 : ℝ) / 2 * (s : ℝ) := h5
        have h9 : (r : ℝ) / s ≥ ((1 : ℝ) / 2 * (s : ℝ)) / (s : ℝ) := by
          apply (div_le_div_iff_of_pos_right h7).mpr
          linarith
        have h10 : ((1 : ℝ) / 2 * (s : ℝ)) / (s : ℝ) = (1 : ℝ) / 2 := by
          field_simp [h7]
          <;> ring
        linarith [h9, h10]
      exact h6
    rw [hx]
    exact h2
