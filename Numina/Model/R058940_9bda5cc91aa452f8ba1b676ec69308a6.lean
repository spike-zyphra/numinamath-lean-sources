import Mathlib

theorem algebra_97331 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) (h : y / (x - z) = (x + y) / z)
    (h' : (x + y) / z = x / y) : x / y = 2 := by
  have h1 : x - z ≠ 0 := by
    intro h2
    have h2' : z = x := by linarith
    contradiction
  have h4 : y * z = (x + y) * (x - z) := by
    have h5 : x - z ≠ 0 := h1
    have h6y : y ≠ 0 := by nlinarith
    have h6z : z ≠ 0 := by nlinarith
    field_simp [h5, h6y, h6z] at h ⊢
    nlinarith
    all_goals
      try { linarith } <;> try { tauto }
      all_goals
        try { 
          have : y ≠ 0 := by nlinarith
          nlinarith 
        }
  have h8 : y * (x + y) = x * z := by
    have h6z : z ≠ 0 := by nlinarith
    have h6y : y ≠ 0 := by nlinarith
    field_simp [h6z, h6y] at h' ⊢
    nlinarith
    all_goals
      try { linarith } <;> try { tauto }
    all_goals
      try { 
        have : y ≠ 0 := by nlinarith
        nlinarith
      }
  have h5 : x / y = 2 := by
    have h19 : (x / y - 2) * (y) = 0 := by
      have : (x / y - 2) * (y) = x - 2 * y := by
        have h6y : y ≠ 0 := by nlinarith
        field_simp [h6y]
        <;> nlinarith
      rw [this]
      have h6 : x - 2 * y = 0 := by
        nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (y - z), sq_nonneg (x - z), sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
      nlinarith
    cases' (mul_eq_zero.mp h19) with h15 h16
    · -- $x / y - 2 = 0$
      field_simp at h15 ⊢
      all_goals nlinarith
    · -- $y = 0$
      exfalso
      have h1y : y = 0 := by linarith
      linarith
  exact h5
  all_goals try { 
    try { 
      have h21 : z ≠ 0 := by nlinarith
      field_simp [h21]
    } 
    <;> try { ring_nf }
    <;> try { nlinarith }
    all_goals try { 
      have h21 : z ≠ 0 := by nlinarith
      have h22 : y ≠ 0 := by nlinarith
      field_simp [h21, h22]
      <;> try { tauto }
    }
    all_goals try { 
      have : y ≠ 0 := by nlinarith
      nlinarith 
    }
    all_goals try { nlinarith }
    all_goals try { try { tauto } }
  }
  all_goals try { 
    try { 
      have h6y : y ≠ 0 := by nlinarith
      have h6z : z ≠ 0 := by nlinarith
      field_simp [h6y, h6z]
    } 
    <;> try { ring_nf }
    <;> try { tauto }
    all_goals try { 
      have h21 : z ≠ 0 := by nlinarith
      have h22 : y ≠ 0 := by nlinarith
      field_simp [h21, h22]
      <;> try { tauto }
    }
    all_goals try { 
      have h6y : y ≠ 0 := by nlinarith
      nlinarith 
    }
    all_goals try { 
      have : y ≠ 0 := by nlinarith
      field_simp
    }
    <;> try { tauto } <;> try { ring_nf }
  }