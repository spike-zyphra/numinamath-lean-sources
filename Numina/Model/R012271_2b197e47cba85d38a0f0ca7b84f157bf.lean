import Mathlib
open Nat Real Finset Set
noncomputable section

theorem number_theory_600028 : IsLeast { q | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≠ b ∧ b ≠ c ∧
  a ≠ c ∧ q = (a * b * c : ℚ) / (a + b + c) } 1 := by 
  constructor
  · -- We can take $a = 1, b = 2, c = 3$, then $\frac{1 \cdot 2 \cdot 3}{1 + 2 + 3} = \frac{6}{6} = 1$.
    use 1, 2, 3 
    all_goals norm_num 
  · -- If $q \in \mathbb{Q}$ is in the set, then $q \geq 1$.
    intro q hq 
    rcases hq with ⟨a, b, c, ha, hb, hc, hne₁, hne₂, hne₃, hq⟩ 
    have h1 : (a * b * c : ℚ) / (a + b + c) ≥ (1 : ℚ) := by 
      have h5 : a * b * c ≥ a + b + c := by
        have h1 : a ≥ 1 := by linarith
        have h2 : b ≥ 1 := by linarith
        have h3 : c ≥ 1 := by linarith
        by_cases h4 : a ≤ 3
        · by_cases h5 : b ≤ 3
          · by_cases h6 : c ≤ 3
            · -- If a ≤ 3, b ≤ 3, c ≤ 3, then {a,b,c} = {1,2,3}.
              have h7 : a ≤ 3 := h4
              have h8 : b ≤ 3 := h5
              have h9 : c ≤ 3 := h6
              have h10 : a = 1 ∨ a = 2 ∨ a = 3 := by
                omega
              have h11 : b = 1 ∨ b = 2 ∨ b = 3 := by
                omega
              have h12 : c = 1 ∨ c = 2 ∨ c = 3 := by
                omega
              rcases h10 with ha' | ha' | ha' <;> rcases h11 with hb' | hb' | hb' <;> rcases h12 with hc' | hc' | hc' 
              <;> 
                subst a b c 
              <;> norm_num at *
              <;> try { contradiction }
              all_goals
                omega 
            · -- If a ≤ 3, b ≤ 3, c > 3.
              have h10 : c > 3 := by linarith
              have h13 : a ≤ 3 := h4
              have h14 : b ≤ 3 := h5
              interval_cases a <;> interval_cases b 
              all_goals 
                omega 
          · -- If a ≤ 3, b > 3.
            have h10 : b > 3 := by linarith
            by_cases h6 : c ≤ 3
            · -- If a ≤ 3, b > 3, c ≤ 3.
              have h13 : a ≤ 3 := h4
              have h14 : c ≤ 3 := h6
              interval_cases a <;> interval_cases c 
              all_goals 
                omega 
            · -- If a ≤ 3, b > 3, c > 3.
              have h10 : b > 3 := by linarith
              have h11 : c > 3 := by linarith
              have h13 : a ≤ 3 := h4
              interval_cases a <;> 
                try { 
                  nlinarith [mul_pos (show 0 < (b: ℕ) by nlinarith) (show 0 < (c: ℕ) by nlinarith)]
                } 
        · -- If a > 3.
          have h10 : a > 3 := by linarith
          by_cases h5 : b ≤ 3
          · -- If a > 3, b ≤ 3.
            by_cases h6 : c ≤ 3
            · -- If a > 3, b ≤ 3, c ≤ 3.
              have h13 : b ≤ 3 := h5
              have h14 : c ≤ 3 := h6
              interval_cases b <;> interval_cases c 
              all_goals 
                omega 
            · -- If a > 3, b ≤ 3, c > 3.
              have h10 : c > 3 := by linarith
              have h13 : b ≤ 3 := h5
              interval_cases b <;> 
                try { 
                  nlinarith [mul_pos (show 0 < (a: ℕ) by nlinarith) (show 0 < (c: ℕ) by nlinarith)]
                } 
          · -- If a > 3, b > 3.
            have h10 : b > 3 := by linarith
            by_cases h6 : c ≤ 3
            · -- If a > 3, b > 3, c ≤ 3.
              have h13 : c ≤ 3 := h6
              interval_cases c <;> 
                try { 
                  nlinarith [mul_pos (show 0 < (a: ℕ) by nlinarith) (show 0 < (b: ℕ) by nlinarith)]
                } 
            · -- If a > 3, b > 3, c > 3.
              have h10 : c > 3 := by linarith
              nlinarith [mul_pos (show 0 < (a: ℕ) by nlinarith) (show 0 < (b: ℕ) by nlinarith), 
                      mul_pos (show 0 < (b: ℕ) by nlinarith) (show 0 < (c: ℕ) by nlinarith)]
      have h14 : (a * b * c : ℚ) ≥ (a + b + c : ℚ) := by 
        exact_mod_cast h5
      have h15 : (a + b + c : ℚ) > 0 := by 
        have ha' : (a : ℚ) ≥ 1 := by exact_mod_cast (show a ≥ 1 by linarith)
        have hb' : (b : ℚ) ≥ 1 := by exact_mod_cast (show b ≥ 1 by linarith)
        have hc' : (c : ℚ) ≥ 1 := by exact_mod_cast (show c ≥ 1 by linarith)
        linarith
      apply (le_div_iff₀ (by positivity)).mpr 
      linarith 
    linarith [hq, h1]