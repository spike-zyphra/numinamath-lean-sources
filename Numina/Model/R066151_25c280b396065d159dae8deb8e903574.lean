import Mathlib

theorem number_theory_132517 : Odd (3^10) ∧ ¬(∃ n, n^3 = 3^10) ∧ ∃ m, m^2 = 3^10 := by 
  constructor
  · -- Show that $3^{10}$ is odd
    have h : Odd (3 ^ 10) := by
      use 29524
      all_goals norm_num
    exact h
  constructor
  · -- Show that $3^{10}$ is not a cube
    intro h
    rcases h with ⟨n, hn⟩
    have h1 : n ^ 3 = 3 ^ 10 := hn
    have h2 : n ≤ 39 := by
      by_contra h
      push_neg at h
      have h3 : n ^ 3 ≥ 40 ^ 3 := by
        have h4 : n ≥ 40 := by linarith
        have h5 : n ^ 3 ≥ 40 ^ 3 := by
          apply pow_le_pow_left
          all_goals nlinarith
        exact h5
      nlinarith
      all_goals nlinarith
    interval_cases n <;> omega
  · -- Show that $3^{10}$ is a square
    use 3 ^ 5
    all_goals norm_num