import Mathlib

theorem algebra_296651 (f : ℝ → ℝ) (hf : f = fun x => 1 / x) (g : ℝ → ℝ)
    (hg : g = fun x => 3 / (4 * x)) (A B : ℝ) (hA : f A = g A) (hB : f B = g B)
    (hAB : A ≠ B) :
    √((A - B) ^ 2 + (g A - g B) ^ 2) = √2 := by
  have eq1 : 1 / A = 3 / (4 * A) := by
    rw [hf] at hA
    rw [hg] at hA
    simpa using hA
  have eq2 : 1 / B = 3 / (4 * B) := by
    rw [hf] at hB
    rw [hg] at hB
    simpa using hB
  by_cases hA0 : A = 0
  · -- Case A = 0 
    have hA0' : A = 0 := hA0
    by_cases hB0 : B = 0
    · -- Case A = 0 and B = 0 
      exfalso 
      exact hAB (by 
        rw [hA0']
        all_goals 
          linarith [hB0]
      )
    · -- Case A = 0 and B ≠ 0 
      have hBn0 : B ≠ 0 := by 
        intro h 
        apply hB0 
        exact h
      have eq3 : (1 / B) = (3 / (4 * B)) := by 
        simpa using eq2
      have eq4 : (4 : ℝ) = (3 : ℝ) := by
        have h1 : B ≠ 0 := hBn0
        field_simp at eq3 ⊢ 
        <;> linarith
      linarith 
  · -- Case A ≠ 0 
    have hAn0 : A ≠ 0 := by 
      intro h 
      apply hA0 
      exact h
    have eq3 : (1 / A) = (3 / (4 * A)) := by 
      simpa using eq1
    have eq4 : (4 : ℝ) = (3 : ℝ) := by
      have h1 : A ≠ 0 := hAn0
      field_simp at eq3 ⊢ 
      <;> linarith
    linarith