import Mathlib

theorem algebra_183707 {a b c : ℝ × ℝ} (ha : a ≠ (0, 0)) (hb : b ≠ (0, 0)) (hc : c ≠ (0, 0))
    (h1 : ¬Collinear ℝ {a, b}) (h2 : ¬Collinear ℝ {a, c}) (h3 : ¬Collinear ℝ {b, c})
    (h4 : ∃ k, (a.1 + b.1) * k = c.1 ∧ (a.2 + b.2) * k = c.2)
    (h5 : ∃ m, (b.1 + c.1) * m = a.1 ∧ (b.2 + c.2) * m = a.2) :
    a.1 + b.1 + c.1 = 0 ∧ a.2 + b.2 + c.2 = 0 := by

  rcases h4 with ⟨k, h11, h12⟩
  rcases h5 with ⟨m, h21, h22⟩

  exfalso
  apply h1
  apply collinear_pair
  <;> try { contradiction }
  <;> try { linarith }
  <;> try { 
    apply collinear_pair 
    <;> try { contradiction }
    <;> try { linarith }
  }
  <;> try { 
    exfalso
    apply h2
    apply collinear_pair 
    <;> try { contradiction }
    <;> try { linarith }
  }
  <;> try { 
    exfalso
    apply h3
    apply collinear_pair 
    <;> try { contradiction }
    <;> try { linarith }
  }
  <;> try { 
    nlinarith [sq_pos_of_ne_zero (show (a.1 ^ 2 + a.2 ^ 2) ≠ 0 by
        by_contra h
        have : a = (0, 0) := by
          simp [Prod.ext_iff] at *
          constructor <;> nlinarith
        contradiction
      ), sq_pos_of_ne_zero (show (b.1 ^ 2 + b.2 ^ 2) ≠ 0 by
        by_contra h
        have : b = (0, 0) := by 
          simp [Prod.ext_iff] at *
          constructor <;> nlinarith
        contradiction
      ), sq_pos_of_ne_zero (show (c.1 ^ 2 + c.2 ^ 2) ≠ 0 by
        by_contra h
        have : c = (0, 0) := by 
          simp [Prod.ext_iff] at *
          constructor <;> nlinarith
        contradiction
      )
    ]
  }
  <;> try { tauto }