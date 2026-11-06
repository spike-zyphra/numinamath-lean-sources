import Mathlib

theorem number_theory_226812 :
    {(p, q, r) : ℕ × ℕ × ℕ | p.Prime ∧ q.Prime ∧ r.Prime ∧ q > r ∧ p > q ∧ p^2 - (q + r)^2 = 136} = {(19, 13, 2)} := by
  ext ⟨p, q, r⟩
  simp
  constructor
  · -- First, proving the existence implication
    rintro ⟨h_p, h_q, h_r, h_qr, h_pq, heq⟩
    have eq1 : p^2 = (q + r)^2 + 136 := by 
      omega
    have h2 : p > q + r := by 
      by_contra h 
      push_neg at h 
      have h3 : p ≤ q + r := by omega 
      have h4 : p^2 ≤ (q + r)^2 := by 
        nlinarith [h3] 
      nlinarith 
    have h3 : p ≤ 68 := by
      nlinarith [sq_nonneg (p + (q + r : ℕ)), sq_nonneg (p - (q + r + 1 : ℕ)), 
        sq_nonneg ((q + r) : ℕ), 
        h2, sq_nonneg ((p) : ℕ)
      ]
    have h4 : (q + r) ≤ 68 := by
      nlinarith [sq_nonneg (p + (q + r : ℕ)), sq_nonneg (p - (q + r + 1 : ℕ)), 
        sq_nonneg ((q + r) : ℕ), 
        h2, sq_nonneg ((p) : ℕ)
      ]
    have h5 : p ≤ 68 := h3 
    have h6 : (q + r) ≤ 68 := h4 
    interval_cases p <;> norm_num at eq1 h_p <;> try { 
      omega 
    } 
    <;> try { 
      have h4 : (q + r) ≤ 68 := by omega 
      interval_cases h1 : (q + r) <;> norm_num at eq1 
      <;> try { 
        have h8 : r < q := by omega 
        have h9 : r ≤ 68 := by omega 
        have h10 : q ≤ 68 := by omega 
        interval_cases r <;> norm_num at h_r 
        <;> try { 
          omega 
        } 
        <;> interval_cases q <;> norm_num at h_q h_r 
        <;> tauto 
      } 
    }
  · -- Backward direction
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    all_goals 
      norm_num 
    all_goals 
      tauto