import Mathlib

open Real

theorem algebra_309795 : tan (π / 9) * tan (2 * π / 9) * tan (π / 3) +
    1 / tan (7 * π / 18) + tan (2 * π / 9) = sqrt 3 := by 
  have htan1 : tan (π / 3) = sqrt 3 := by 
    rw [tan_pi_div_three]
  have htan2 : 1 / tan (7 * π / 18) = tan (π / 9) := by 
    have h1 : 7 * π / 18 = π / 2 - π / 9 := by 
      linarith [pi_pos]
    rw [h1]
    rw [tan_pi_div_two_sub]
    <;> field_simp
    all_goals 
      try { 
        linarith [pi_pos]
        all_goals 
          try { 
            nlinarith [pi_pos]
          } 
          all_goals 
            try { 
              tauto
            }
          all_goals 
            try { 
              nlinarith [pi_pos]
            }
        }
  rw [htan1, htan2]

  have htan3 : tan (π / 9 + 2 * π / 9) = sqrt 3 := by 
    have htan31 : π / 9 + 2 * π / 9 = π / 3 := by 
      linarith [pi_pos]
    rw [htan31]
    rw [tan_pi_div_three]

  have h1 : π / 9 ≠ (2 * (0 : ℤ) + 1) * π / 2 := by 
    linarith [pi_pos]

  have h2 : 2 * π / 9 ≠ (2 * (0 : ℤ) + 1) * π / 2 := by 
    linarith [pi_pos]

  have h3 : ∀ (k : ℤ), π / 9 ≠ (2 * k + 1) * π / 2 := by 
    intro k 
    by_contra h 
    have eq1 : π / 9 = (2 * k + 1) * π / 2 := by 
      linarith 
    have eq2 : (2 * (k : ℝ) + 1 : ℝ) * (π / 2 : ℝ) = π / 9 := by 
      linarith [eq1] 
    have h20 : π ≠ 0 := pi_ne_zero
    have eq3 : 2 * (k : ℝ) + 1 = 2 / 9 := by 
      have h1 : π ≠ 0 := pi_ne_zero
      apply (mul_left_inj' h1).mp
      nlinarith 
    have eq4 : (k : ℝ) < (1 : ℝ) / 10 := by 
      linarith 
    have eq5 : k < 1 := by 
      by_contra h 
      push_neg at h 
      have hk : (k : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h 
      linarith 
    have eq6 : k > -1 := by 
      by_contra h 
      push_neg at h 
      have h30 : (k : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h 
      nlinarith [pi_pos] 
    have eq40 : k = 0 := by 
      linarith 
    rw [eq40] at eq3 
    norm_num at eq3 
    all_goals 
      try { 
        linarith [pi_pos]
        all_goals try { 
          nlinarith [pi_pos]
          all_goals try { 
            exfalso <;> try { 
                linarith [pi_pos]
            }
          }
        }
      }
      all_goals try { 
        nlinarith [pi_pos]
        all_goals try { 
          exfalso <;> try { 
            nlinarith 
          }
        }
      }
      all_goals try { 
        exfalso <;> try { 
          nlinarith 
        }
      }
      all_goals try { 
        nlinarith [pi_pos]
      }
      all_goals try { 
        nlinarith [pi_pos]
      }
      all_goals try { 
        linarith [pi_pos]
      }
      all_goals try { 
        nlinarith [pi_pos]
      }
      all_goals try { 
        exfalso
      }
      all_goals try { 
        nlinarith [pi_pos]
      }
      all_goals try { 
        exfalso 
      }
      all_goals try { 
        nlinarith [pi_pos]
      }
      all_goals try { 
        tauto 
        all_goals try { 
          nlinarith [pi_pos]
        }
      }
      all_goals try { 
        tauto 
      }
      all_goals try { 
        nlinarith [pi_pos]
      }
      all_goals try { 
        tauto 
      }
      all_goals try { 
        exfalso <;> try { 
          nlinarith 
        }
      }
      all_goals try { 
        nlinarith [pi_pos]
      }
    all_goals try { 
      tauto 
      all_goals try { 
        nlinarith [pi_pos]
      }
    }
    all_goals try { 
      tauto 
      all_goals try { 
        nlinarith [pi_pos]
      }
      all_goals try { 
        nlinarith [pi_pos]
      }
    }
    all_goals try { 
      nlinarith [pi_pos]
      all_goals try { 
        tauto 
        all_goals try { 
          nlinarith [pi_pos]
        }
      }
    }
    
    all_goals try { 
      nlinarith [pi_pos]
    }
    all_goals try { 
      nlinarith [pi_pos]
    }
    all_goals try { 
      nlinarith [pi_pos]
    }

  have h4 : ∀ (l : ℤ), 2 * π / 9 ≠ (2 * l + 1) * π / 2 := by 
    intro l 
    by_contra h 
    have eq1 : 2 * π / 9 = (2 * l + 1) * π / 2 := by 
      linarith 
    have eq2 : (2 * (l : ℝ) + 1 : ℝ) * (π / 2 : ℝ) = 2 * π / 9 := by 
      linarith [eq1] 
    have h1 : π ≠ 0 := pi_ne_zero 
    have eq3 : 2 * (l : ℝ) + 1 = 4 / 9 := by 
      have h2 : π ≠ 0 := pi_ne_zero 
      apply (mul_left_inj' h2).mp 
      nlinarith 
    have eq4 : (l : ℝ) < (1 : ℝ) / 4 := by 
      linarith 
    have eq5 : l < 1 := by 
      by_contra h 
      push_neg at h 
      have h9 : (l : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h 
      linarith 
    have eq6 : l > -1 := by 
      by_contra h 
      push_neg at h 
      have h30 : (l : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h 
      nlinarith [pi_pos] 
    have h40 : l = 0 := by 
      linarith 
    rw [h40] at eq3 
    norm_num at eq3 
    all_goals try { 
      linarith [pi_pos]
      all_goals try { 
        nlinarith [pi_pos]
        all_goals try { 
          exfalso
        }
      }
    }
    all_goals try { 
      nlinarith [pi_pos]
    }
    all_goals try { 
      exfalso <;> try { 
        nlinarith 
        all_goals try { 
          tauto 
          all_goals try { 
            nlinarith [pi_pos]
          }
        }
      }
    }
    all_goals try { 
      nlinarith [pi_pos]
    }
    all_goals try { 
      tauto 
    }
    all_goals try { 
      nlinarith [pi_pos, mul_pos pi_pos pi_pos]
    }
    all_goals try { 
      tauto
    }
  -- Apply tan_add formula
  have htan4 : tan (π / 9 + 2 * π / 9) = (tan (π / 9) + tan (2 * π / 9)) / (1 - tan (π / 9) * tan (2 * π / 9)) := by 
    rw [tan_add]
    <;> try { 
      tauto 
    }
    <;> all_goals try { 
      apply h3
      all_goals try { 
        nlinarith [pi_pos]
      }
    }
    all_goals try { 
      apply h4 
      all_goals try { 
        nlinarith [pi_pos]
      }
    }
  have htan5 : (tan (π / 9) + tan (2 * π / 9)) / (1 - tan (π / 9) * tan (2 * π / 9)) = sqrt 3 := by 
    rw [← htan3, htan4]
  
  -- Manipulate equation to get sqrt 3 * (1 - tan (π / 9) * tan (2 * π / 9)) = tan (π / 9) + tan (2 * π / 9)
  have h6 : sqrt 3 * (1 - tan (π / 9) * tan (2 * π / 9)) = tan (π / 9) + tan (2 * π / 9) := by 
    have h7 : (tan (π / 9) + tan (2 * π / 9)) / (1 - tan (π / 9) * tan (2 * π / 9)) = sqrt 3 := htan5
    have h8 : 1 - tan (π / 9) * tan (2 * π / 9) ≠ 0 := by 
      by_contra h9 
      rw [h9] at h7 
      field_simp at h7 
      <;> nlinarith [pi_pos, sqrt_nonneg (3 : ℝ), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      <;> omega 
    field_simp at h7 ⊢ 
    all_goals 
      try { 
        nlinarith 
        all_goals try { 
          exfalso 
          <;> try { 
            nlinarith
          }
          all_goals try { 
            tauto 
          }
          all_goals try { 
            nlinarith 
          }
        }
      }
      all_goals try { 
        nlinarith [pi_pos, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        all_goals try { 
          tauto 
        }
      }
      all_goals try { 
        exfalso 
        <;> try { 
          nlinarith 
        }
        <;> try { 
          tauto 
        }
      }
      all_goals try { 
        tauto 
        all_goals try { 
          nlinarith [pi_pos, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        }
      }
      all_goals try { 
        nlinarith [pi_pos, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        all_goals try { 
          tauto 
        }
      }
      all_goals try { 
        exfalso <;> try { 
          nlinarith 
        }
        <;> tauto 
      }
      all_goals try { 
        nlinarith [pi_pos, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      }
  -- Final simplification 
  have htan7 : tan (π / 9) * tan (2 * π / 9) * sqrt 3 + (tan (π / 9) + tan (2 * π / 9)) = sqrt 3 := by 
    have h6' : sqrt 3 * (1 - tan (π / 9) * tan (2 * π / 9)) = tan (π / 9) + tan (2 * π / 9) := h6 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  nlinarith [htan7, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  all_goals try { 
    nlinarith [pi_pos]
    all_goals try { 
      exfalso <;> try { 
          nlinarith 
          all_goals try { 
            tauto 
          }
      }
    }
  }
  all_goals try { 
    nlinarith [pi_pos]
    all_goals try { 
      exfalso
    }
    all_goals try { 
      nlinarith
    }
    all_goals try { 
      exfalso
      <;> try { 
        nlinarith
      }
      <;> try { 
        tauto 
      }
    }
  }