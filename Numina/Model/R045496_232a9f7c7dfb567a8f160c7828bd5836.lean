import Mathlib

theorem number_theory_84612 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ x y : ℕ, 0 < x → 0 < y → x^(a + b) + y = x^a * y^b ↔ (x, y) = (2, 4)) :
    (a, b) = (1, 2) := by
  have h1 := h 2 4
  norm_num at h1
  have h2 := h 1 1
  norm_num [Prod.ext_iff] at h2
  all_goals
    try { tauto }
    <;> try { 
      exfalso <;> try { tauto } <;> try { 
        have h3 := h 2 0
        norm_num [Prod.ext_iff] at h3
      }
    }
  all_goals
    try { 
      exfalso <;> try { 
        have h4 := h 0 0
        norm_num [Prod.ext_iff] at h4 
      }
    }
  all_goals
    try { 
      omega
    }
  all_goals
    try { 
      exfalso <;> try { tauto } <;> try { 
        have h5 := h 1 2
        norm_num at h5
        all_goals try { tauto } <;> try { tauto } <;> try { exfalso } <;> try { tauto }
      }
    }
  all_goals
    try { 
      exfalso <;> try { 
        have h6 := h 1 2
        norm_num at h6
        all_goals try tauto
        all_goals try { 
          have h7 := h 2 1
          norm_num at h7
          all_goals tauto
        }
      }
    }
  all_goals
    try { 
      exfalso <;> try { 
        have h8 := h 4 2
        norm_num at h8
        all_goals try { tauto } 
        all_goals try { 
          have h9 := h 4 2
          norm_num at h9
          all_goals try tauto
        }
      }
    }
  all_goals
    try { 
      exfalso <;> try { 
        have h10 := h 2 1
        norm_num at h10
        all_goals try { tauto }
      }
    }
  all_goals
    try { 
      exfalso <;> try { 
        have h11 := h 1 4
        norm_num at h11
        all_goals try { tauto }
      }
    }
  all_goals
    try { 
      exfalso <;> try { 
        have h12 := h 4 0
        norm_num [Prod.ext_iff] at h12
        all_goals try { tauto }
      }
    }
  all_goals
    try { 
      exfalso <;> try { 
        have h13 := h 0 4
        norm_num [Prod.ext_iff] at h13
        all_goals try { tauto }
      }
    }