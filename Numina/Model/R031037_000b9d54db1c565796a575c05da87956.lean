import Mathlib

theorem number_theory_247375 (a : ℕ) (ha : 1 ≤ a ∧ a ≤ 9) :
    ∃ x y, x ≠ 0 ∧ y ≠ 0 ∧ 1 / x - 1 / y = a / 9 := by
  rcases ha with ⟨ha1, ha2⟩
  interval_cases a <;> try { 
    use 6, 18
    all_goals
      norm_num 
    all_goals 
      try { 
        native_decide 
      }
  }
  <;> try { 
    use 10, 15
    all_goals 
      norm_num 
    all_goals 
      try { 
        native_decide 
      }
  }
  <;> try { 
    use 3, 6
    all_goals 
      norm_num 
    all_goals 
      try { 
        native_decide 
      }
  }
  <;> try { 
    use 9, 12
    all_goals 
      norm_num 
    all_goals 
      try { 
        native_decide 
      }
  }
  <;> try { 
    use 2, 3
    all_goals 
      norm_num 
    all_goals 
      try { 
        native_decide 
      }
  }
  <;> try { 
    use 1, 2
    all_goals 
      norm_num 
    all_goals 
      try { 
        native_decide 
      }
  }
  <;> try { 
    use 10, 15
    all_goals 
      norm_num 
    all_goals 
      try { 
        native_decide 
      }
  }
  <;> try { 
    use 10, 18
    all_goals 
      norm_num 
    all_goals 
      try { 
        native_decide 
      }
  }
  <;> try { 
    use 3, 6
    all_goals 
      norm_num 
    all_goals 
      try { 
        native_decide 
      }
  }
  <;> try { 
    native_decide 
  }