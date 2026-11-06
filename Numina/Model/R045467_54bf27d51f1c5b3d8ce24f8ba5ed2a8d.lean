import Mathlib

open Real

theorem algebra_146565 {f : ℝ → ℝ} (hf : f = fun x => (1 + x) / (1 - x)) :
    ∀ x, x ≠ 1 → x ≠ -1 → f (-x) = 1 / f x := by
  intro x hx hx'
  have h1 : f (-x) = (1 - x) / (1 + x) := by
    rw [hf]
    ring_nf
    <;> field_simp [(show (1 + x) ≠ 0 by
        intro h
        apply hx'
        linarith
      ), (show (1 - x) ≠ 0 by
        intro h
        apply hx
        linarith
      )
    ]
    <;> ring
  have h2 : 1 / f x = (1 - x) / (1 + x) := by
    rw [hf]
    have h3 : (1 + x) ≠ 0 := by 
      intro h
      apply hx'
      linarith
    have h4 : (1 - x) ≠ 0 := by 
      intro h
      apply hx
      linarith
    field_simp [h3, h4]
    <;> ring_nf
    <;> field_simp [h3, h4]
    <;> ring
  rw [h1, h2]
  <;> ring_nf
  <;> field_simp [(show (1 + x) ≠ 0 by
    intro h
    apply hx'
    linarith
  ), (show (1 - x) ≠ 0 by
    intro h
    apply hx
    linarith
  )
  ]
  <;> ring