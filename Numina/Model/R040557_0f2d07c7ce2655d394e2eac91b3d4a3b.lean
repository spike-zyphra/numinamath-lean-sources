import Mathlib

theorem algebra_212423 {a : ℕ → ℕ} (ha1 : a 1 = 6)
    (han : ∀ n > 0, a (n + 1) + n + 1 = 2 * (a n + 1)) :
    (∑ i in Finset.Icc 1 2022, a i) % 10 = 8 := by
  have h3 : ∀ n > 0, a (n + 1) = 2 * a n + 1 - n := by
    intro n hn
    specialize han n hn
    omega
  have h1' : ∀ n, a (n + 1) = 5 * 2 ^ n + (n + 1 : ℕ) := by
    intro n 
    induction n with 
    | zero =>
      simp [ha1]
      <;> try { omega } <;> try { native_decide }
    | succ n ih =>
      have eq1 := h3 (n + 1) (by linarith)
      simp [show n + 1 + 1 = n + 2 by omega] at eq1 ⊢
      simp [ih] at eq1 ⊢
      <;> try { 
        ring_nf at eq1 ⊢ 
        <;> omega 
      }
      <;> try { 
        omega 
      }
      all_goals try { 
        tauto 
      }
      all_goals try { 
        nlinarith 
      }
      all_goals try { 
        native_decide 
      }
  -- Now establishing closed-form for the sum.
  have h4 : ∀ (n : ℕ), ∑ i in Finset.Icc 1 n, a i = 5 * (2 ^ n - 1) + n * (n + 1) / 2 := by
    intro n 
    induction n with 
    | zero =>
      simp [ha1]
      <;> try { 
        omega 
      }
      all_goals try { 
        tauto 
      }
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [h1' (n)]
      simp [ih]
      <;> ring_nf <;> omega 
      all_goals try { 
        tauto 
      }
      all_goals try { 
        nlinarith 
      }
      all_goals try { 
        native_decide 
      }
  have h5 : (∑ i in Finset.Icc 1 2022, a i) % 10 = 8 := by
    rw [h4 2022]
    norm_num
    <;> try { native_decide }
    all_goals try { 
      tauto 
    }
    all_goals try { 
      tauto 
    }
    all_goals try { 
      nlinarith 
    }
    all_goals try { 
      native_decide 
    }
    all_goals try { 
      try { native_decide } 
    }
    all_goals try { 
      tauto 
      <;> nlinarith 
    }
  exact h5
  <;> try { native_decide }
  all_goals try { 
    try { tauto } 
    <;> omega 
  }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    tauto 
  }
  all_goals try { 
    tauto 
    <;> try { native_decide } 
    <;> try { tauto } 
    <;> try { nlinarith } 
    <;> try { native_decide } 
    <;> try { tauto } 
    <;> try { native_decide } 
    <;> try { 
      all_goals try { 
        tauto 
      } 
    }
  }
  all_goals try { 
    try { native_decide } 
    <;> try { tauto } 
    <;> try { nlinarith } 
    <;> try { tauto } 
  }
  all_goals try { 
    tauto 
  }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    tauto 
  }
  all_goals try { 
    try { native_decide }
  }
  all_goals try { 
    tauto 
  }
  all_goals try { 
    tauto 
  }
  all_goals try { 
    try { native_decide } 
    <;> try { 
      omega 
    } 
    <;> try { 
      tauto 
    } 
    <;> try { 
      nlinarith 
    } 
    <;> try { 
      tauto 
    } 
  }
  all_goals try { 
    try { native_decide } 
    <;> try { 
      tauto 
    } 
    <;> try { 
      nlinarith 
    } 
    <;> try { 
      tauto 
    } 
  }