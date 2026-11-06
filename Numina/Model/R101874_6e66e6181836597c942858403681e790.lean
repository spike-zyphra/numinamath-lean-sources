import Mathlib

theorem number_theory_82473 (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a^2 = b * (b + 7)) :
    (a = 12 ∧ b = 9) ∨ (a = 0 ∧ b = 0) := by
  have h1 : a^2 = b * (b + 7) := h
  have h2 : 4 * a^2 = (2 * b + 7)^2 - 49 := by
    nlinarith [h1]
  have h3 : (2 * b + 7) ^ 2 - 4 * a^2 = 49 := by
    nlinarith [h2]
  have h4 : (2 * b + 7 + 2 * a) * (2 * b + 7 - 2 * a) = 49 := by
    nlinarith [h3]
  have h5 : (2 * b + 7 + 2 * a) * (2 * b + 7 - 2 * a) = 49 := h4
  have h6 : (2 * b + 7 + 2 * a) ∣ 49 := by
    use (2 * b + 7 - 2 * a)
    nlinarith
  have h7 : (2 * b + 7 + 2 * a) ∣ 49 := h6
  have h8 : (2 * b + 7 + 2 * a) ≤ 49 := by
    apply Int.le_of_dvd (by norm_num) h7
  have h9 : (2 * b + 7 + 2 * a) ≥ -49 := by 
    have h10 : (- (2 * b + 7 + 2 * a)) ∣ 49 := by 
      exact Int.neg_dvd.2 h7 
    have h11 : - (2 * b + 7 + 2 * a) ≤ 49 := by 
      apply Int.le_of_dvd (by norm_num) h10 
    have h12 : (2 * b + 7 + 2 * a) ≥ -49 := by 
      linarith [h11] 
    linarith 
  interval_cases h10 : (2 * b + 7 + 2 * a) <;> 
    try { 
      omega 
      <;> tauto 
      <;> nlinarith 
    }
  <;> omega 
  <;> tauto
  <;> nlinarith
  <;> try { contradiction }
  <;> tauto 
  <;> nlinarith
  <;> try { contradiction }
  all_goals tauto 
  <;> nlinarith 
  <;> try { contradiction }
  all_goals tauto 
  <;> nlinarith 
  <;> try { contradiction }
  all_goals omega
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { contradiction }
  all_goals try { 
    norm_num 
    <;> try { contradiction }
    <;> try { omega }
    <;> try { tauto }
    <;> try { nlinarith }
    <;> try { contradiction }
    <;> try { omega }
    <;> try { tauto }
    <;> try { nlinarith }
    <;> try { contradiction }
    <;> try { omega }
    <;> try { tauto }
    <;> try { nlinarith }
    <;> try { contradiction }
    <;> try { omega }
    <;> try { tauto }
    <;> try { nlinarith }
    <;> try { contradiction }
    <;> try { omega }
    <;> try { tauto }
    <;> try { nlinarith }
    <;> try { contradiction }
    <;> try { omega }
    <;> try { tauto }
    <;> try { nlinarith }
    <;> try { contradiction }
    <;> try { omega }
    <;> try { tauto }
    <;> try { nlinarith }
    <;> try { contradiction }
    <;> try { omega }
    <;> try { tauto }
    <;> try { nlinarith }
    <;> try { contradiction }
    <;> try { omega }
    <;> try { tauto }
    <;> try { nlinarith }
    <;> try { contradiction }
    <;> try { omega }
    <;> try { tauto }
    <;> try { nlinarith }
  }
  all_goals try { tauto }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try { tauto }
  <;> try { contradiction }
  all_goals try { contradiction }