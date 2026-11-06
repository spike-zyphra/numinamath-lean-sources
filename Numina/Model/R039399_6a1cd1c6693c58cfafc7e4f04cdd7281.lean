import Mathlib

theorem algebra_21628 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hroots : {x | x^2 + a * x + b = 0} = {b + 1, a + 1}) :
    a+1 = 3 / 2 ∧ b+1 = -2 := by

  have h1: (a+1)^2+a*(a+1)+b = 0 := by
    have: a+1 ∈ {x | x^2 + a * x + b = 0} := by
      rw [hroots]; simp
    exact this
  have h2: (b+1)^2+a*(b+1)+b = 0 := by
    have: b+1 ∈ {x | x^2 + a * x + b = 0} := by
      rw [hroots]; simp
    exact this
  have h1': (a+1)*(a+1) - (-a)*(a+1)+b = 0 := by
    rw [← h1]; ring
  have h2': (b+1)*(b+1) - (-a)*(b+1)+b = 0 := by
    rw [← h2]; ring
  have aadd := vieta_formula_quadratic h1'
  have badd := vieta_formula_quadratic h2'
  -- use Vieta's formula.
  rcases aadd with ⟨d,hd⟩
  have deq: d = b+1 := by
    have hh1: d ∈ {x | x^2 + a * x + b = 0} := by
      simp; linarith [hd.left]
    rw [hroots] at hh1; simp at hh1
    by_cases hab: a = b
    · rw [hab] at hh1; tauto
    · push_neg at hab
      rcases badd with ⟨e,he⟩
      have hh2: e ∈ {x | x^2 + a * x + b = 0} := by
          simp; linarith [he.left]
      rw [hroots] at hh2; simp at hh2
      rcases hh2 with heb | hea
      · rcases hh1 with hdb | hda
        · tauto
        · have: a+1 + (a+1) = b+1 + (b+1) := by
            linarith [hd.left, he.left]
          have: a = b := by nlinarith
          tauto
      · rcases hh1 with hdb | hda
        · linarith
        · exfalso; nlinarith
  -- let Lean's formal tactics solve the remaining steps
  have ha1 : a + 1 = 3 / 2 := by 
    nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, 
      h1, h2, 
      sq_nonneg (a - 1 / 2), sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (b - 0)]
  have hb1 : b + 1 = -2 := by
    nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, 
      h1, h2, 
      sq_nonneg (a - 1 / 2), sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (b - 0)]
  constructor
  · exact ha1
  · exact hb1