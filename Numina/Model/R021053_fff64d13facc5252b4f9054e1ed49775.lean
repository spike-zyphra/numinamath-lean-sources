import Mathlib

theorem number_theory_176606 (d : ℤ) : ∃ m n : ℤ, d = (n - 2 * m + 1) / (m ^ 2 - n) := by
  by_cases h2 : d = -1
  · -- Case where d = -1
    rw [h2]
    use 1
    use 0
    all_goals
    norm_num
  · -- Case where d ≠ -1
    use -d
    use d ^ 2 - d - 1
    have h3 : d + 1 ≠ 0 := by
      intro h4
      apply h2
      linarith
    have h4 : (d ^ 2 - d - 1 - 2 * (-d) + 1 : ℤ) = d ^ 2 + d := by
      ring
    have h7 : ((-d : ℤ) ^ 2 - (d ^ 2 - d - 1) : ℤ) = d + 1 := by
      ring_nf
    rw [h4, h7]
    have h8 : (d ^ 2 + d) / (d + 1) = d := by
      have h9 : (d + 1) ∣ (d ^ 2 + d) := by
        use d
        all_goals ring
      have h9' : (d ^ 2 + d) / (d + 1) = d := by
        rw [show d ^ 2 + d = d * (d + 1) by ring]
        field_simp [show d + 1 ≠ 0 by omega]
        all_goals omega
      linarith
    have eq4 : d = (d ^ 2 + d) / (d + 1) := by
      rw [show (d ^ 2 + d) / (d + 1) = d by exact h8]
    exact eq4