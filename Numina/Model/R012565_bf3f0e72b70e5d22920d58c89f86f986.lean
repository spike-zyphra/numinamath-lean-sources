import Mathlib

theorem algebra_133392 (a b c : ℝ × ℝ × ℝ)
    (h₀ : ¬Coplanar ℝ {a, b, c}) :
    ¬Coplanar ℝ {a + b + c, a + b - c, 2 * a + b + 3 * c} := by 
  have h1 : ¬ Coplanar ℝ {a, b, c} := h₀
  simp [coplanar_triple] at h₀ ⊢
  all_goals
    try { 
      try { 
        aesop
      }
      <;> intro h
      <;> try { 
        exfalso
      }
      <;> try { 
        exfalso
        <;> tauto
      }
      <;> try { 
        ring_nf at h
        ring_nf at h₀
        exfalso
        tauto
      }
    }
  all_goals
    try { 
      intro h
      exfalso
      try { 
        have h2 : (a.1 * (b.2 * c.3 - b.3 * c.2) - a.2 * (b.1 * c.3 - b.3 * c.1) + a.3 * (b.1 * c.2 - b.2 * c.1)) = 0 := by
          nlinarith [h]
        tauto
      }
      try { 
        exfalso
        <;> tauto
      }
      try { 
        norm_num [Finset.sum_insert, Finset.sum_singleton] at h₀ h ⊢
        <;> nlinarith
      }
    }
  all_goals
    try { 
      norm_num [Finset.sum_insert, Finset.sum_singleton] at h₀ ⊢
      all_goals
        try { 
          nlinarith
        }
    }