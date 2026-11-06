import Mathlib

theorem number_theory_637874 {B : ℕ} (hB : B = 4) :
  {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | a < B ∧ b < B ∧ c < B ∧ d < B 
  ∧ (a * B ^ 3 + b * B ^ 2 + c * B + d) - (a * B + b : ℤ) * (c * B + d) 
  = (d * B ^ 3 + c * B ^ 2 + b * B + a) - (d * B + c : ℤ) * (b * B + a)} =
  {(0, 3, 0, 2), (2, 0, 3, 0)} ∪ {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | a < 4 ∧ b < 4 ∧ c < 4 ∧ d < 4 ∧ a = d ∧ b = c} := by 
  ext ⟨a, b, c, d⟩
  constructor
  · simp
    intro h1 h2 h3 h4 h5
    have eq1 : (a - d) * (B ^ 2 + B + 1) + B * (b - c : ℤ) = 
      (B + 1) * (a * c - b * d) := by 
      nlinarith
    simp [hB] at eq1
    rw [hB] at h1 h2 h3 h4
    interval_cases a 
    -- discuss by cases a, and in the each case we  discuss by cases b. (key point : the a b c d are all bounded, so we could discuss by cases easily)
    -- the case a = 0
    interval_cases b
    simp_all [Nat.succ_le_iff]
    have aux1 : (↑d * 21) + (4 * (c : ℤ)) = 0 := by 
      linarith
    norm_cast at aux1
    omega
    simp_all 
    omega
    simp_all
    omega
    simp_all 
    omega
    -- the case a = 1
    interval_cases b
    simp_all
    omega
    simp_all 
    omega
    simp_all 
    omega
    simp_all 
    omega
    -- the case a = 2
    interval_cases b
    simp_all 
    omega
    simp_all 
    omega
    simp_all
    omega
    simp_all 
    omega
    -- the case a = 3
    interval_cases b
    simp_all 
    omega
    simp_all 
    omega
    simp_all
    omega
    simp_all 
    omega
  · simp [hB]
    intro h
    obtain  h | h:= h
    obtain h1| h2 := h
    · obtain ⟨ha, hb, hc, hd⟩ := h1
      simp [ha, hb, hc, hd]
    · obtain ⟨ha, hb, hc, hd⟩ := h2
      simp [ha, hb, hc, hd]
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    simp_all 



    