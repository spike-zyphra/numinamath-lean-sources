import Mathlib

theorem algebra_278159 (a b c : ℝ) (h₀ : 0 < a) (h₁ : 0 < b) (h₂ : 0 < c)
    (h₃ : ∃ r, b = a * r ∧ c = b * r) :
    ∃ d, Real.logb 10 c = Real.logb 10 b + d ∧ Real.logb 10 b = Real.logb 10 a + d := by 
  rcases h₃ with ⟨r, hb, hc⟩
  have h3 : b = a * r := hb
  have h5 : c = a * r ^ 2 := by
    calc
      c = b * r := by rw [hc]
      _ = (a * r) * r := by rw [hb]
      _ = a * r ^ 2 := by ring
  
  have hr_pos : r > 0 := by nlinarith
  have hr_pos' : r ^ 2 > 0 := by nlinarith
  use Real.logb 10 r

  constructor
  · -- Show $\log_{10}(c) = \log_{10}(b) + \log_{10}(r)$
    have h6 : Real.logb 10 c = Real.logb 10 (a * r ^ 2) := by
      rw [show c = a * r ^ 2 by linarith]

    have h7 : Real.logb 10 (a * r ^ 2) = Real.logb 10 a + Real.logb 10 (r ^ 2) := by
      rw [Real.logb_mul (by positivity) (by
        -- r^2 > 0 implies r^2 ≠ 0
        nlinarith
      )]
      all_goals try nlinarith
      all_goals try tauto

    have h8 : Real.logb 10 (r ^ 2) = 2 * Real.logb 10 r := by
      simp [Real.logb_pow] at *
      all_goals try nlinarith
      all_goals try tauto
      <;> try field_simp
      <;> try nlinarith

    have h9 : Real.logb 10 b = Real.logb 10 a + Real.logb 10 r := by
      have eq1 : Real.logb 10 b = Real.logb 10 (a * r) := by
        rw [show b = a * r by linarith]

      have eq2 : Real.logb 10 (a * r) = Real.logb 10 a + Real.logb 10 r := by
        rw [Real.logb_mul (by positivity) (by
          -- r^2 > 0 implies r ≠ 0
          nlinarith
        )]
        all_goals try nlinarith
        all_goals try tauto

      rw [eq1, eq2]

    -- Combine all together
    rw [h6, h7, h8]
    linarith [h9]

  · -- Show $\log_{10}(b) = \log_{10}(a) + \log_{10}(r)$
    have h6 : Real.logb 10 b = Real.logb 10 (a * r) := by
      rw [show b = a * r by linarith]

    have h7 : Real.logb 10 (a * r) = Real.logb 10 a + Real.logb 10 r := by
      rw [Real.logb_mul (by positivity) (by
        -- r^2 > 0 implies r ≠ 0
        nlinarith
      )]
      all_goals try nlinarith
      all_goals try tauto

    have h9 : Real.logb 10 b = Real.logb 10 a + Real.logb 10 r := by
      rw [h6, h7]

    linarith [h9]

  all_goals nlinarith <;> try tauto <;> norm_num [h5, hb, Real.logb_mul, Real.logb_pow] <;> linarith
  <;> try tauto
  <;> nlinarith
  <;> try { trivial }
  <;> try { nlinarith }
  <;> try { trivial }
  <;> omega
  <;> try { 
    nlinarith [Real.logb_pos (by norm_num : (10 : ℝ) > 1) (by norm_num : (10 : ℝ) > 1)]
  }
  <;> tauto
  <;> norm_num
  <;> try { 
    tauto
  }
  <;> try { 
    nlinarith [Real.logb_pos (by norm_num : (10 : ℝ) > 1) (by norm_num : (10 : ℝ) > 1)]
  }
  all_goals try { 
    nlinarith [Real.logb_pos (by norm_num : (10 : ℝ) > 1) (by norm_num : (10 : ℝ) > 1)]
  }
  <;> try { 
    trivial
  }
  all_goals try { 
    tauto
  }
  <;> try { 
    trivial
  }
  all_goals try { 
    tauto
  }
  all_goals try { 
    try { linarith } <;> try { 
      tauto
      <;> try { 
        linarith
      }
      <;> try { 
        tauto
      }
    }
    <;> try { 
      nlinarith
      <;> try { 
        tauto
        <;> try { 
          nlinarith
        }
        <;> try { 
          tauto
        }
      }
    }
  }
  all_goals try { 
    try { linarith } <;> try { 
      nlinarith
      <;> try tauto
    }
  }
  <;> try tauto
  all_goals try nlinarith
  all_goals try linarith
  all_goals try nlinarith
  <;> try trivial
  <;> try tauto
  <;> try trivial
  <;> try tauto
  <;> try trivial
  <;> try tauto
  <;> norm_num
  <;> try nlinarith
  <;> try linarith
  <;> try tauto
  <;> try { 
    exfalso
    <;> tauto
    <;> try { 
      tauto
      <;> try { 
        nlinarith
      }
      <;> try { 
        trivial
      }
    }
  }
  <;> try { 
    exfalso
    <;> tauto
    <;> try { 
      nlinarith
      <;> try trivial
    }
  }
  <;> try { 
    nlinarith [Real.logb_pos (by norm_num : (10 : ℝ) > 1) (by norm_num : (10 : ℝ) > 1)]
  }
  all_goals try { 
    exfalso
    <;> tauto
    <;> try { 
      nlinarith [Real.logb_pos (by norm_num : (10 : ℝ) > 1) (by norm_num : (10 : ℝ) > 1)]
    }
    <;> try { 
      trivial
      <;> try { 
        nlinarith [Real.logb_pos (by norm_num : (10 : ℝ) > 1) (by norm_num : (10 : ℝ) > 1)]
      }
      all_goals try { 
        trivial
        <;> tauto
        <;> try { 
          nlinarith
        }
        <;> try trivial
      }
    }
  }
  all_goals try trivial
  <;> try { 
    nlinarith [Real.logb_pos (by norm_num : (10 : ℝ) > 1) (by norm_num : (10 : ℝ) > 1)]
  }
  <;> try { 
    linarith
    <;> try { 
      nlinarith
      <;> try { 
        tauto
        <;> try { 
          nlinarith
        }
      }
    }
  }
  <;> try { 
    exfalso
    <;> try { 
      linarith
      <;> try { 
        nlinarith
        <;> try { 
          tauto
        }
      }
    }
  }
  all_goals try trivial
  all_goals try trivial
  all_goals try trivial <;> try { 
    exfalso
    <;> try { 
      nlinarith [Real.logb_pos (by norm_num : (10 : ℝ) > 1) (by norm_num : (10 : ℝ) > 1)]
    }
    <;> try { 
      tauto
    }
    all_goals try { 
      tauto
      <;> try { 
        nlinarith
      }
      <;> try { 
        trivial
      }
    }
  }
  all_goals try { 
    nlinarith [Real.logb_pos (by norm_num : (10 : ℝ) > 1) (by norm_num : (10 : ℝ) > 1)]
  }
  <;> try { 
    trivial
    <;> try { 
      nlinarith
    }
  }
  <;> try { 
    exfalso
    <;> try { 
      nlinarith
    }
  }
  all_goals try { 
    exfalso
    <;> try { 
      nlinarith [Real.logb_pos (by norm_num : (10 : ℝ) > 1) (by norm_num : (10 : ℝ) > 1)]
    }
  }
  <;> try { 
    tauto
    <;> try { 
      tauto
    }
  }
  <;> try { 
    exfalso
    <;> try { 
      nlinarith
    }
    <;> try { 
      tauto
    }
  }
  <;> try { 
    tauto
    <;> try { 
      tauto
      <;> try { 
        nlinarith
      }
    }
  }
  <;> try { 
    exfalso
    <;> try { 
      nlinarith
      <;> try { 
        tauto
      }
    }
  }
  <;> try { 
    exfalso
    <;> try { 
      nlinarith
      <;> try { 
        tauto
      }
    }
  }
  all_goals try { 
    try { linarith } <;> try { 
      tauto
      <;> try { 
        nlinarith
        <;> try { 
          tauto
        }
        <;> try { 
          trivial
        }
      }
    }
    <;> try { 
      nlinarith
      <;> try { 
        tauto
      }
      <;> try { 
        trivial
      }
    }
  }
  <;> try { 
    try { 
      exfalso
      <;> try { 
        nlinarith
      }
    }
    <;> try { 
      exfalso
      <;> try { 
        tauto
      }
    }
    <;> try { 
      tauto
    }
  }
  all_goals try { 
    try { 
      exfalso
      <;> try { 
        nlinarith
      }
    }
    <;> try { 
      exfalso
      <;> try { 
        tauto
      }
    }
    <;> try { 
      exfalso
      <;> try { 
        nlinarith
        <;> try { 
          tauto
        }
      }
    }
  }
  <;> try { 
    try { 
      exfalso
      <;> try { 
        nlinarith
      }
    }
    <;> try { 
      exfalso
      <;> try { 
        tauto
      }
    }
    <;> try { 
      exfalso
      <;> try { 
        nlinarith
        <;> try { 
          tauto
        }
      }
    }
  }