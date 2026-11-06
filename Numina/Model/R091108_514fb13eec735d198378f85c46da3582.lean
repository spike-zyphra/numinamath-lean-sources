import Mathlib

theorem algebra_176110 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : ∃ a r, n = 100 * a + 10 * r + a)
    (h₂ : ∃ b c, b ≠ 0 ∧ c ≠ 0 ∧ n = 100 * b + 10 * c + a ∧ b * 10 + c = n - 594)
    (h₃ : ∃ d e, d ≠ 0 ∧ e ≠ 0 ∧ n = 100 * d + 10 * e + a ∧ d * 10 + e = n - 18) :
    n = 842 := by 
  norm_num [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₄, h₅⟩
  have h6 : n ≤ 999 := h₅
  have h7 : 100 ≤ n := h₄
  have h8 : n = 842 := by 
    try { 
      rcases h₁ with ⟨a, r, h⟩
      rcases h₂ with ⟨b, c, hb, hc, h₂₁, h₂₂⟩
      rcases h₃ with ⟨d, e, hd, he, h₃₁, h₃₂⟩
      omega
    }
    <;> try { 
      omega
    }
    <;> try { 
      interval_cases n <;> omega 
    }
    <;> try { 
      exfalso 
      <;> omega 
    }
    <;> try { 
      nlinarith 
    }
    <;> try { 
      omega 
    }
    <;> try { 
      exfalso 
      <;> omega 
    }
    <;> try { 
      interval_cases n <;> omega 
    }
    <;> nlinarith 
  exact h8
  <;> try { 
    omega 
  }
  <;> try { 
    exfalso 
    <;> omega 
  }
  <;> try { 
    interval_cases n <;> omega 
  }
  <;> try { 
    nlinarith 
  }
  <;> try { 
    omega 
  }
  <;> try { 
    exfalso 
    <;> omega 
  }
  <;> try { 
    interval_cases n <;> omega 
  }
  <;> try { 
    nlinarith 
  }
  <;> try { 
    exfalso 
    <;> omega 
  }
  <;> try { 
    interval_cases n <;> omega 
  }