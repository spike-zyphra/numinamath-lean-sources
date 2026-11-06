import Mathlib
open Real

theorem number_theory_8168 :
IsLeast {s : ℕ | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 2002 ∧ s = a + b + c} 38 := by
  constructor
  · -- Show 38 is in the set
    use 11, 13, 14
    all_goals norm_num
  · -- Show that 38 is the minimum
    intro s hs
    rcases hs with ⟨a, b, c, ha, hb, hc, h1, h3⟩
    by_contra h
    push_neg at h
    have h4 : a ≤ 36 := by
      have h3a : a + b + c ≤ 37 := by
        omega
      nlinarith [show a ≤ 36 by nlinarith [h3, h, show b + c ≥ 2 by nlinarith [show b ≥ 1 by omega, show c ≥ 1 by omega]
        ]
      ]
    have h5 : b ≤ 36 := by
      have h3a : a + b + c ≤ 37 := by
        omega
      nlinarith [show b ≤ 36 by nlinarith [h3, h, show a + c ≥ 2 by nlinarith [show a ≥ 1 by omega, show c ≥ 1 by omega]
        ]
      ]
    have h6 : c ≤ 36 := by
      have h3a : a + b + c ≤ 37 := by
        omega
      nlinarith [show c ≤ 36 by nlinarith [h3, h, show a + b ≥ 2 by nlinarith [show a ≥ 1 by omega, show b ≥ 1 by omega]
        ]
      ]
    interval_cases a <;> try { 
      omega 
      <;> interval_cases b <;> try { 
        omega 
        <;> interval_cases c <;> try { 
          omega 
        }
      }
    }
    <;> interval_cases b <;> try { 
      omega 
      <;> interval_cases c <;> try { 
        omega 
        <;> interval_cases a <;> try { 
          omega 
        }
      }
    }
    <;> interval_cases c <;> try { 
      omega 
      <;> interval_cases a <;> try { 
        omega 
        <;> interval_cases b <;> try { 
          omega 
        }
      }
    }
    <;> interval_cases a <;> try { 
      omega 
      <;> interval_cases b <;> try { 
        omega 
        <;> interval_cases c <;> try { 
          omega 
        }
      }
    }
    <;> interval_cases b <;> try { 
      omega 
      <;> interval_cases c <;> try { 
        omega 
        <;> interval_cases a <;> try { 
          omega 
        }
      }
    }
    <;> interval_cases c <;> try { 
      omega 
      <;> interval_cases a <;> try { 
        omega 
        <;> interval_cases b <;> try { 
          omega 
        }
      }
    }