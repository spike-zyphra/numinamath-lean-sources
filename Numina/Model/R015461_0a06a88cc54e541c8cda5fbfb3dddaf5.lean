import Mathlib

theorem inequalities_3200 (a b c : ℝ) :
  |a| + |b| + |c| - |a + b| - |b + c| - |c + a| + |a + b + c| ≥ 0 := by
  cases' abs_cases a with ha ha <;> 
      cases' abs_cases b with hb hb <;> 
        cases' abs_cases c with hc hc <;> 
          cases' abs_cases (a + b) with hab hab <;> 
            cases' abs_cases (b + c) with hbc hbc <;> 
              cases' abs_cases (c + a) with hac hac <;> 
                cases' abs_cases (a + b + c) with habc habc 
                <;> try { linarith }
  all_goals try { linarith }
  all_goals try { 
    linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg (a + b), abs_nonneg (b + c), abs_nonneg (c + a), abs_nonneg (a + b + c)]
  }
  <;> try { linarith }
  <;> try { norm_num }
  <;> try { linarith }
  <;> try { 
    linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg (a + b), abs_nonneg (b + c), abs_nonneg (c + a), abs_nonneg (a + b + c)]
  }
  <;> try { linarith }
  <;> try { 
    linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg (a + b), abs_nonneg (b + c), abs_nonneg (c + a), abs_nonneg (a + b + c)]
  }
  <;> try { linarith }
  <;> try { 
    linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg (a + b), abs_nonneg (b + c), abs_nonneg (c + a), abs_nonneg (a + b + c)]
  }
  all_goals try { linarith }
  all_goals try { 
    linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg (a + b), abs_nonneg (b + c), abs_nonneg (c + a), abs_nonneg (a + b + c)]
  }