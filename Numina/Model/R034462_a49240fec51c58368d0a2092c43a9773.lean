import Mathlib

open Real

theorem algebra_244946 {a b : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (h : ∀ n, ∑ k in Finset.Icc 1 n, (a n)^2 + 2 * a n = n / (n + 1))
    (hb : ∀ n, b n = a n / (1 - sqrt (2 * n * (n + 1) * a n))) :
    (∀ n, 0 < n → b n > 4) ∧
    (∃ m, 0 < m ∧ ∀ n > m, ∑ k in Finset.Icc 1 n, a (n + 1) / a n < n - 2021) := by
  have h1 := h 0
  norm_num [Finset.sum_eq_zero] at h1
  all_goals 
    try { 
      have h2 := ha 0
      norm_num at h2 ⊢ 
      all_goals linarith 
    }
    <;> try { 
      exfalso 
      <;> 
      try { 
        norm_num [hb 0] 
      } 
      <;> 
      try { 
        nlinarith [ha 0] 
      } 
    }
    <;> try { 
      intro n hn 
      norm_num [hb n] at *
      all_goals 
        try { 
          linarith [ha n, ha 0] 
        } 
      <;> 
      try { 
        norm_num 
      } 
      <;> 
      try { 
        nlinarith [ha n, ha 0] 
      } 
      <;> 
      try { 
        exfalso 
        <;> 
        norm_num 
        <;> 
        nlinarith 
      } 
    }
    <;> try { 
      use 0 
      norm_num 
      <;> 
      intro n hn 
      have h1 := h 0 
      norm_num [Finset.sum_eq_zero] at h1 
      all_goals 
        try { 
          simp 
          all_goals linarith [ha 0, ha n] 
        } 
      <;> 
      try { 
        exfalso 
        <;> 
        norm_num 
        <;> 
        all_goals 
          try { 
            nlinarith 
          } 
        <;> 
        try { 
          exfalso 
        }
      } 
    }
  <;> try { 
    exfalso 
    <;> 
    norm_num 
    <;> 
    all_goals 
      try { 
        nlinarith 
      } 
    <;> 
    norm_num 
    <;> 
    all_goals 
      try { 
        linarith 
      } 
    <;> 
    norm_num 
  }