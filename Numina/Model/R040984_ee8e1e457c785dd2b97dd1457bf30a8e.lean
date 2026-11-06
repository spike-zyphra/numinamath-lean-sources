import Mathlib

theorem number_theory_210978 (a b : ℕ) (h₀ : a + b = 770) :
    ¬(a * b ∣ 770) := by
  intro h
  have h1 : a ≤ 770 := by
    omega
  have h4 : b = 770 - a := by 
    omega
  rw [h4] at h
  interval_cases a <;> try { 
    omega 
  } <;> try { 
    norm_num at h h₀ ⊢
    all_goals
      try { 
        tauto 
      }
    all_goals
      try { 
        omega 
      }
  }
  <;> try { 
    tauto 
  }
  <;> try { 
    all_goals 
      try { 
        tauto 
      }
  }
  <;> try { 
    nlinarith 
    all_goals
    try { 
      tauto 
    }
  }
  <;> try { 
    tauto 
    all_goals
    try { 
      tauto 
    }
  }