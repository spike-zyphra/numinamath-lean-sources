import Mathlib

theorem number_theory_97060 :
    {(p, q) : ℕ × ℕ | p.Prime ∧ q.Prime ∧ p + q = 47}.ncard = 0 := by
  have h1 : {(p, q) : ℕ × ℕ | p.Prime ∧ q.Prime ∧ p + q = 47} = ∅ := by
    ext ⟨p, q⟩
    simp
    intro hp hq hsum
    have h2 : p ≤ 47 := by linarith
    have h3 : q ≤ 47 := by linarith
    interval_cases p <;> interval_cases q
    <;> norm_num at hp hq hsum
    <;> all_goals
      contradiction
  rw [h1]
  simp