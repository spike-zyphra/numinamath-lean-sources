import Mathlib

theorem inequalities_90562
    (a b c : ℝ)
    (h₀ : abs (a - b) ≥ abs c)
    (h₁ : abs (b - c) ≥ abs a)
    (h₂ : abs (c - a) ≥ abs b) :
    a = b + c ∨ b = a + c ∨ c = a + b := by
  cases' abs_cases (a - b) with h h <;> cases' abs_cases c with k k <;> 
    cases' abs_cases (b - c) with m m <;> cases' abs_cases a with n n <;> 
      cases' abs_cases (c - a) with p p <;> cases' abs_cases b with q q <;> 
        try { 
          first
            | left; linarith
            | right; left; linarith
            | right; right; linarith
          all_goals tauto
          all_goals nlinarith
          <;> try { linarith }
          <;> try { 
            first
              | left; linarith
              | right; left; linarith
              | right; right; linarith
          }
          all_goals try { 
            first
              | left; linarith
              | right; left; linarith
              | right; right; linarith
          }
          all_goals try { linarith }
          all_goals try { nlinarith }
          <;> try { tauto }
          <;> try { tauto }
        } <;> try { try { tauto } <;> try { linarith } <;> try { nlinarith } }
  <;> try { try { tauto } <;> try { linarith } <;> try { nlinarith } }
  all_goals try { try { tauto } <;> try { linarith } <;> try { nlinarith } }
  <;> try { try { tauto } <;> try { linarith } <;> try { nlinarith } }
  all_goals try { nlinarith }
  <;> try { try { nlinarith } }
  all_goals try { nlinarith }
  <;> try { try { tauto } <;> try { linarith } <;> try { nlinarith } }
  <;> try { try { tauto } <;> try { nlinarith } }
  <;> try { try { tauto } <;> try { linarith } <;> try { nlinarith } }
  <;> try { tauto } <;> try { linarith }
  <;> try { nlinarith }
  <;> try { tauto }
  <;> try { linarith }
  <;> try { nlinarith }