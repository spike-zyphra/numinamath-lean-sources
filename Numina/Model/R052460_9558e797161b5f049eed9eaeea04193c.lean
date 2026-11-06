import Mathlib

theorem algebra_310300 {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x > y)
    (h : x + y + x * y = 80) : x = 26 := by 
  have h1 : x * y + x + y = 80 := by linarith
  have h2 : (x + 1) * (y + 1) = 81 := by 
    nlinarith
  have h5 : y + 1 ∣ 81 := by
    use x + 1
    linarith [h2]
  have h7 : y + 1 ≤ 81 := by 
    exact Int.le_of_dvd (by omega) h5 
  have h6 : y ≤ 80 := by nlinarith
  
  have h_pos : y + 1 > 0 := by linarith

  have h3 : (y + 1 = 1 ∨ y + 1 = 3 ∨ y + 1 = 9 ∨ y + 1 = 27 ∨ y + 1 = 81) := by 
    have h4 : y + 1 ∣ 81 := h5
    have h5 : y + 1 ∣ (81 : ℤ) := h4
    have h6 : y + 1 ≥ 0 := by omega
    have h7 : y + 1 ≤ 81 := by apply Int.le_of_dvd (by omega) h4
    
    interval_cases k : y + 1 <;> norm_num at h5 h6 h7 <;> tauto 
    <;> norm_num at h5 h6 h7 <;> try { contradiction } <;> omega
  
  rcases h3 with (h8 | h8 | h8 | h8 | h8)
  · -- Case y + 1 = 1
    have h9 : y = 0 := by linarith
    have : (x > 0) := hx
    have : (y > 0) := by linarith
    omega 
  · -- Case y + 1 = 3
    have h9 : y = 2 := by linarith
    have h10 : x + 1 = 27 := by
      rw [h8] at h2
      nlinarith 
    have h11 : x = 26 := by linarith
    linarith 
  · -- Case y + 1 = 9
    have h9 : y = 8 := by linarith 
    have h10 : x + 1 = 9 := by
      rw [h8] at h2
      nlinarith 
    have h11 : x = 8 := by linarith
    omega 
  · -- Case y + 1 = 27
    have h9 : y = 26 := by linarith 
    have h10 : x + 1 = 3 := by 
      rw [h8] at h2
      nlinarith 
    have h11 : x = 2 := by linarith 
    omega 
  · -- Case y + 1 = 81
    have h9 : y = 80 := by linarith 
    have h10 : x + 1 = 1 := by 
      rw [h8] at h2
      nlinarith 
    have h11 : x = 0 := by linarith 
    omega 
  all_goals 
    try { contradiction }
    <;> omega 
    <;> norm_num 
    <;> try { contradiction } 
    <;> linarith 
    <;> try { contradiction }
    <;> omega