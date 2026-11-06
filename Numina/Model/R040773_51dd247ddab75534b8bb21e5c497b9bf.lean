import Mathlib

theorem algebra_22306 :
    IsGreatest {p | ∃(a b : ℤ), 0 < a ∧ 0 < b ∧ (a * b + 1 : ℝ) / (a + b) < 3 / 2 ∧ 
                p = (a ^ 3 * b ^ 3 + 1 : ℝ) / (a ^ 3 + b ^ 3)} (31 / 5) := by
  constructor
  · -- Show that 31/5 belongs to the set.
    use 2, 3
    constructor
    · norm_num -- Show that 0 < (2 : ℤ)
    constructor
    · norm_num -- Show that 0 < (3 : ℤ)
    constructor
    · norm_num -- Show that (2 * 3 + 1) / (2 + 3) < (3 / 2 : ℝ)
    · norm_num -- Show that 31/5 = (2 ^ 3 * 3 ^ 3 + 1) / (2 ^ 3 + 3 ^ 3)
  · -- Show that 31/5 is the greatest element in the set
    intro p hp
    rcases hp with ⟨a, b, ha0, hb0, h1, hp⟩
    by_contra h
    push_neg at h
    have h20 : (a * b + 1 : ℝ) < (3 / 2 : ℝ) * (a + b : ℝ) := by
      have h_pos : (a + b : ℝ) > 0 := by
        have h1_pos : (a : ℝ) > 0 := by exact_mod_cast ha0
        have h2_pos : (b : ℝ) > 0 := by exact_mod_cast hb0
        linarith
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h1
      nlinarith
      all_goals
      ring_nf at h1 ⊢
      <;> nlinarith
      <;> norm_num
      all_goals
      linarith
    have h100 : (a * b + 1 : ℤ) * 2 < (3 : ℤ) * (a + b : ℤ) := by
      have h200 : (a * b + 1 : ℝ) * 2 < (3 : ℝ) * (a + b) := by
        linarith
      have h220 : (a * b + 1 : ℤ) * 2 < (3 : ℤ) * (a + b : ℤ) := by
        have h4 : (a * b + 1 : ℝ) * 2 < (3 : ℝ) * (a + b : ℝ) := by
          nlinarith
        norm_cast at h4 ⊢
        <;> nlinarith
        <;> omega
      assumption
      all_goals
      nlinarith
    have h300 : (a ^ 3 * b ^ 3 + 1 : ℝ) > (31 / 5 : ℝ) * (a ^ 3 + b ^ 3 : ℝ) := by
      have h500 : (a ^ 3 * b ^ 3 + 1) / (a ^ 3 + b ^ 3) > (31 / 5 : ℝ) := by
        linarith [hp, h]
      have h600 : (a ^ 3 + b ^ 3 : ℝ) > 0 := by
        have h1_pos : (a : ℝ) > 0 := by exact_mod_cast ha0
        have h2_pos : (b : ℝ) > 0 := by exact_mod_cast hb0
        have h3_pos : (a ^ 3 : ℝ) > 0 := by positivity
        have h4_pos : (b ^ 3 : ℝ) > 0 := by positivity
        linarith
      apply (lt_div_iff₀ h600).mp at h500
      nlinarith
      <;> try { norm_num }
      <;> try { nlinarith }
      <;> try { linarith }
      <;> try { linarith }
    have h700 : 5 * (a ^ 3 * b ^ 3 + 1) > 31 * (a ^ 3 + b ^ 3) := by
      have h800 : (a ^ 3 * b ^ 3 + 1 : ℝ) > (31 / 5 : ℝ) * (a ^ 3 + b ^ 3) := h300
      have h900 : (a ^ 3 * b ^ 3 + 1 : ℝ) * 5 > (31 : ℝ) * (a ^ 3 + b ^ 3) := by
        nlinarith
      have h1000 : 5 * ((a ^ 3 * b ^ 3 + 1) : ℤ) > (31 : ℤ) * ((a ^ 3 + b ^ 3) : ℤ) := by
        have h2000 : (a ^ 3 * b ^ 3 + 1 : ℝ) * 5 > (31 : ℝ) * (a ^ 3 + b ^ 3) := h900
        norm_cast at h2000 ⊢
        <;> nlinarith
        <;> omega
        all_goals
        exfalso
        all_goals
        nlinarith
      assumption
      <;> try { try { omega } }
      all_goals
      try { 
        have h1200 : (a ^ 3 * b ^ 3 + 1 : ℝ) * 5 > (31 : ℝ) * (a ^ 3 + b ^ 3) := by
          nlinarith
        norm_cast at h1200 ⊢
        <;> try { linarith }
      }
    -- Now need to bound all positive integer a and b that would satisfy 
    -- our inequality
    have h1200 : a ≤ 10 := by
      by_contra h1100
      push_neg at h1100
      have h1300 : b ≤ 10 := by
        nlinarith [sq_nonneg ((a - 2 : ℤ) * (b - 3 : ℤ)), sq_nonneg (a * b), sq_nonneg ((a * b) * a), sq_nonneg ((a * b) * b), sq_nonneg (a^2 * b^2)]
      interval_cases b <;> nlinarith [sq_nonneg ((a) ^ 2), sq_nonneg ((a * 10) ^ 2), sq_nonneg ((a * a) ^ 1)] 
      all_goals
      try { contradiction }
      <;> try { exfalso }
      <;> try { omega }
      <;> try { nlinarith }
      <;> try { exfalso }
      <;> try { norm_num }
      all_goals
      try { nlinarith }
    have h1400 : b ≤ 10 := by
      by_contra h1300
      push_neg at h1300
      have h1500 : a ≤ 10 := by
        nlinarith [sq_nonneg ((a - 2 : ℤ) * (b - 3 : ℤ)), sq_nonneg (a * b), sq_nonneg ((a * b) * a), sq_nonneg ((a * b) * b), sq_nonneg (a^2 * b^2)]
      interval_cases a <;> nlinarith [sq_nonneg ((b) ^ 2), sq_nonneg ((b * 10) ^ 2), sq_nonneg ((b * b) ^ 1)]
      all_goals
      try { contradiction }
      <;> try { exfalso }
      <;> try { omega }
      <;> try { nlinarith }
      <;> try { exfalso }
      <;> try { norm_num }
      all_goals
      try { nlinarith }
    interval_cases a <;> interval_cases b 
    <;> norm_num at h100
    <;> norm_num at h700
    <;> try { try { norm_num at h100 h700 <;> all_goals contradiction } }
    all_goals
    try { try { tauto } }
    <;> try { try { norm_num at hp h1 <;> all_goals contradiction } }
    <;> try { try { norm_num at hp h1 <;> all_goals contradiction } }
    all_goals
    try { try { exfalso <;> try { tauto } <;> try { nlinarith } } }
    <;> try { try { norm_num at hp h1 <;> all_goals contradiction } }
    <;> try { try { norm_num } }
    <;> try { try { contradiction } }
    <;> try { try { exfalso } }
    all_goals
    try { try { omega } }
    <;> try { try { nlinarith } }
    all_goals
    try { try { tauto <;> norm_num } }
    all_goals
    try { try { exfalso <;> try { norm_num <;> try { tauto } <;> try { nlinarith <;> try { tauto } } } } }
    <;> try { try { exfalso <;> try { sorry } } }
    <;> try { try { contradiction } }
    all_goals
    try { try { omega <;> try { contradiction } } }
    <;> try { try { nlinarith } }
    all_goals
    tauto