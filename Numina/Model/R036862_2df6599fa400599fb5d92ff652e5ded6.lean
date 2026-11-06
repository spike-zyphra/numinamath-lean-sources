import Mathlib
open Real Set


theorem inequalities_9495 : {a : ℝ | ∃ f : ℝ → ℝ, (∀ x, f x = x^3 - a * x + 2) ∧ (∀ x ∈ Icc (-1) 1, f x ≥ 0)} = Icc (-1) 3 := by 
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- Assume the existence of such a function, proving $a \in [-1,3]$
    rintro ⟨f, hf_def, hf⟩
    have h1 := hf 1 (by norm_num)
    have h1' : f 1 ≥ 0 := by simpa using h1
    rw [hf_def 1] at h1'
    have h2 := hf (-1) (by norm_num)
    have h2' : f (-1) ≥ 0 := by simpa using h2
    rw [hf_def (-1)] at h2'
    constructor
    · -- Prove -1 ≤ a
      nlinarith
    · -- Prove a ≤ 3
      nlinarith
  · -- Assume $a \in [-1,3]$, proving the existence of such a function
    rintro ⟨ha1, ha2⟩
    use fun x => x^3 - a * x + 2
    constructor
    · -- Show $f x = x^3 - a * x + 2$
      intro x
      rfl
    · -- Show $f x \geq 0$ for all $x \in [-1, 1]$
      intro x hx
      rcases hx with ⟨hx1, hx2⟩
      have h3 : x^3 - a * x + 2 ≥ 0 := by
        nlinarith [sq_nonneg (x^2 - a / 3), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x - a / 3), sq_nonneg (a * x), sq_nonneg ((x - 1) * (x + 1)), sq_nonneg (x^2 - 1), sq_nonneg ((x - 1)^2)]
      simp [h3]
      all_goals nlinarith