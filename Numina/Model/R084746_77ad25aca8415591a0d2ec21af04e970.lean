import Mathlib

theorem algebra_254103 (total_population : ℕ) (h : total_population ≠ 0)
    (women_votes_percentage : ℝ) (women_percentage : ℝ)
    (h1 : women_votes_percentage = 40 / 100) (h2 : women_percentage = 52 / 100) :
    (women_votes_percentage * women_percentage * total_population) / total_population = 20.8 / 100 := by
  have h3 : (women_votes_percentage * women_percentage * total_population) / total_population = 20.8 / 100 := by
    rw [h1, h2]
    have h4 : (total_population : ℝ) ≠ 0 := by
      exact_mod_cast h
    field_simp [h4]
    <;> ring_nf <;> norm_num
    all_goals
      try { tauto }
      <;> try { norm_num }
      all_goals
        try { nlinarith }
        <;> try { tauto }
  exact h3