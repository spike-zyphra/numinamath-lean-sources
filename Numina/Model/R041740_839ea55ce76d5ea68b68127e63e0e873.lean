import Mathlib

theorem number_theory_239364 : 
    ∀ (m : ℤ), m ∈ Set.Icc (-6 : ℤ) 6 → ∃ (k : ℤ), 
      (k + (3 - 1) / 2 - (k + (3 - 1) / 2) % 3) + 
      (2*k + (5 - 1) / 2 - (2*k + (5 - 1) / 2) % 5) + 
      (3*k + (7 - 1) / 2 - (3*k + (7 - 1) / 2) % 7) - 6*k = m := by
  intro m hm
  rcases hm with ⟨hm1, hm2⟩
  have h1 : m ≥ -6 := by linarith
  have h2 : m ≤ 6 := by linarith
  interval_cases m <;> try { 
    use 0; all_goals omega 
  }
  <;> try { 
    use 1; all_goals omega 
  }
  <;> try { 
    use 2; all_goals omega 
  }
  <;> try { 
    use 3; all_goals omega 
  }
  <;> try { 
    use 4; all_goals omega 
  }
  <;> try { 
    use 5; all_goals omega 
  }
  <;> try { 
    use 6; all_goals omega 
  }
  <;> try { 
    use -1; all_goals omega 
  }
  <;> try { 
    use -2; all_goals omega 
  }
  <;> try { 
    use -3; all_goals omega 
  }
  <;> try { 
    use -4; all_goals omega 
  }
  <;> try { 
    use -5; all_goals omega 
  }
  <;> try { 
    use -6; all_goals omega 
  }
  <;> try { 
    use 31; all_goals omega 
  }
  <;> try { 
    use 66; all_goals omega 
  }
  <;> try { 
    use -27; all_goals omega 
  }
  <;> try { 
    use 7; all_goals omega 
  }
  <;> try { 
    use 44; all_goals omega 
  }
  <;> try { 
    use 89; all_goals omega 
  }
  <;> try { 
    use 74; all_goals omega 
  }
  <;> try { 
    use -31; all_goals omega 
  }
  <;> try { 
    use 12; all_goals omega 
  }
  <;> try { 
    use -15; all_goals omega 
  }
  <;> try { 
    use -12; all_goals omega 
  }
  <;> try { 
    use 28; all_goals omega 
  }
  <;> try { 
    use -21; all_goals omega 
  }