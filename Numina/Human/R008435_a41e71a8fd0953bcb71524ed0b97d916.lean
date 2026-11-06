import Mathlib

/- The solution set of the inequality $|x^2-2|<2$ is ( )\nA: $(-1,1)$\nB: $(-2,2)$\nC: $(-1,0) \\cup (0,1)$\nD: $(-2,0) \\cup (0,2)$ -/
theorem inequalities_575707 : {x : ℝ | abs (x^2 - 2) < 2} = Set.Ioo (-2) 0 ∪ Set.Ioo 0 2 := by
  ext x
  simp [abs_lt]
  constructor
  . rintro ⟨h₁, h₂⟩
    obtain h | h | h : x < 0 ∨ x = 0 ∨ 0 < x := lt_trichotomy x 0
    . refine Or.inl ⟨?_, h⟩
      nlinarith
    . simp [h] at h₁
    . refine Or.inr ⟨h, ?_⟩
      nlinarith
  . rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    all_goals
      constructor <;> nlinarith
