import Mathlib


theorem number_theory_188511 (a b c : ℕ) (ha : 0 < a) (h : a ≤ b ∧ b ≤ c)
    (h' : 4 * (a + b + c) = a * b * c) :
    (a, b, c) = (1, 5, 24) ∨ (a, b, c) = (1, 6, 14) ∨ (a, b, c) = (1, 8, 9) ∨
    (a, b, c) = (2, 3, 10) ∨ (a, b, c) = (2, 4, 6) := by
  rcases h with ⟨hab, hbc⟩
  have h1 : a ≤ b := hab
  have h2 : b ≤ c := hbc
  have h3 : a ≤ 4 := by
    nlinarith [h', mul_pos ha (show 0 < b by nlinarith [hab, ha]), mul_pos (show 0 < b by nlinarith [hab, ha]) (show 0 < c by nlinarith [hbc, hab, ha]), sq_nonneg (a - 2 : ℤ), sq_nonneg (b - 4 : ℤ), sq_nonneg (c - 10 : ℤ)
      ]
  interval_cases a <;> try {
    have h5 : b ≤ 12 := by
      nlinarith [h', sq_nonneg (b - 12 : ℤ), sq_nonneg (c - 24 : ℤ)
        ]
    interval_cases b <;> try { 
      norm_num [Prod.ext_iff] at h' ⊢
      all_goals
      try { 
        omega
      }
    }
  }