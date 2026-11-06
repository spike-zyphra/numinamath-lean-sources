import Mathlib

theorem algebra_5469 (x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z + x * y + x * z + y * z + x + y + z = 454) : x + y + z = 22 := by
  have eq1 : (x + 1) * (y + 1) * (z + 1) = 455 := by
    nlinarith
  have h2 : (x + 1) ∣ 455 := by
    use (y + 1) * (z + 1)
    all_goals nlinarith [eq1]
  have h3 : (y + 1) ∣ 455 := by
    use (x + 1) * (z + 1)
    all_goals nlinarith [eq1]
  have h4 : (z + 1) ∣ 455 := by
    use (x + 1) * (y + 1)
    all_goals nlinarith [eq1]
  have hx2 : x + 1 ≥ 2 := by omega
  have hy2 : y + 1 ≥ 2 := by omega
  have hz2 : z + 1 ≥ 2 := by omega
  have h5 : (x + 1) = 5 ∨ (x + 1) = 7 ∨ (x + 1) = 13 ∨ (x + 1) = 35 ∨ (x + 1) = 65 ∨ (x + 1) = 91 ∨ (x + 1) = 455 := by
    have h50 : (x + 1) ≤ 455 := by
      exact Int.le_of_dvd (by norm_num) h2
    interval_cases h51 : (x + 1) <;> try { tauto }
    all_goals omega
  rcases h5 with h5 | h5 | h5 | h5 | h5 | h5 | h5
  · -- x +1 =5
    have hx10 : x = 4 := by 
      omega
    have eq2 : (y + 1) * (z + 1) = 91 := by
      rw [show (x + 1 : ℤ) = 5 by linarith [h5]] at eq1
      nlinarith
    have eq3 : (y + 1) ∣ 91 := by
      use (z + 1)
      all_goals nlinarith [eq2]
    have hy1 : (y + 1) = 7 ∨ (y + 1) = 13 := by 
      have h60 : (y + 1) ≤ 91 := by
        exact Int.le_of_dvd (by norm_num) eq3
      have h61 : (y + 1) ≥ 2 := by
        omega
      interval_cases h62 : (y + 1) <;> try { 
        omega
      }
      all_goals try { tauto }
    rcases hy1 with hy1 | hy1
    · -- y + 1 = 7
      have hy10 : y = 6 := by
        omega
      have eq4 : (z + 1 : ℤ) = 13 := by
        nlinarith [eq2, hy1]
      have hz10 : z = 12 := by 
        omega
      omega
    · -- y + 1 = 13
      have hy2 : y = 12 := by
        omega
      have eq5 : (z + 1 : ℤ) = 7 := by
        nlinarith [eq2, hy1]
      have hz2 : z = 6 := by
        omega
      omega
  · -- x +1 =7
    have hx10 : x = 6 := by 
      omega
    have eq2 : (y + 1) * (z + 1) = 65 := by
      rw [show (x + 1 : ℤ) = 7 by linarith [h5]] at eq1
      nlinarith
    have eq3 : (y + 1) ∣ 65 := by
      use (z + 1)
      all_goals nlinarith [eq2]
    have hy1 : (y + 1) = 5 ∨ (y + 1) = 13 := by 
      have h60 : (y + 1) ≤ 65 := by
        exact Int.le_of_dvd (by norm_num) eq3
      have h61 : (y + 1) ≥ 2 := by
        omega
      interval_cases h62 : (y + 1) <;> try { 
        omega
      }
      all_goals try { tauto }
    rcases hy1 with hy1 | hy1
    · -- y + 1 = 5
      have hy10 : y = 4 := by
        omega
      have eq4 : (z + 1 : ℤ) = 13 := by
        nlinarith [eq2, hy1]
      have hz10 : z = 12 := by 
        omega
      omega
    · -- y + 1 = 13
      have hy2 : y = 12 := by
        omega
      have eq5 : (z + 1 : ℤ) = 5 := by
        nlinarith [eq2, hy1]
      have hz4 : z = 4 := by
        omega
      omega
  · -- x +1 =13
    have hx10 : x = 12 := by 
      omega
    have eq2 : (y + 1) * (z + 1) = 35 := by
      rw [show (x + 1 : ℤ) = 13 by linarith [h5]] at eq1
      nlinarith
    have eq3 : (y + 1) ∣ 35 := by
      use (z + 1)
      all_goals nlinarith [eq2]
    have hy1 : (y + 1) = 5 ∨ (y + 1) = 7 := by 
      have h60 : (y + 1) ≤ 35 := by
        exact Int.le_of_dvd (by norm_num) eq3
      have h61 : (y + 1) ≥ 2 := by
        omega
      interval_cases h62 : (y + 1) <;> try { 
        omega
      }
      all_goals try { tauto }
    rcases hy1 with hy1 | hy1
    · -- y + 1 = 5
      have hy4 : y = 4 := by
        omega
      have eq4 : (z + 1 : ℤ) = 7 := by
        nlinarith [eq2, hy1]
      have hz6 : z = 6 := by 
        omega
      omega
    · -- y + 1 = 7
      have hy6 : y = 6 := by
        omega
      have eq5 : (z + 1 : ℤ) = 5 := by
        nlinarith [eq2, hy1]
      have hz4 : z = 4 := by
        omega
      omega
  · -- x +1 =35
    have eq21 : (y + 1) * (z + 1) = 13 := by
      rw [show (x + 1 : ℤ) = 35 by linarith [h5]] at eq1
      nlinarith
    have hy4 : (y + 1) ∣ 13 := by
      use (z + 1)
      all_goals nlinarith [eq21]
    have hy52 : (y + 1) ≤ 13 := by
      exact Int.le_of_dvd (by norm_num) hy4
    have hy53 : (y + 1) ≥ 2 := by
      omega
    interval_cases h531 : (y + 1) <;> try { 
      omega
    } <;> try { tauto } <;> try { linarith } 
    all_goals try { linarith }
  · -- x +1 =65
    have eq6 : (y + 1) * (z + 1) = 7 := by
      rw [show (x + 1 : ℤ) = 65 by linarith [h5]] at eq1
      nlinarith
    have hy21 : (y + 1) ∣ 7 := by
      use (z + 1)
      all_goals nlinarith [eq6]
    have hy22 : (y + 1) ≤ 7 := by
      exact Int.le_of_dvd (by norm_num) hy21
    have hy23 : (y + 1) ≥ 2 := by
      omega
    interval_cases h44 : (y + 1) <;> try { 
      omega
    } <;> try { tauto } <;> try { linarith }
  · -- x +1 =91
    have eq8 : (y + 1) * (z + 1) = 5 := by
      rw [show (x + 1 : ℤ) = 91 by linarith [h5]] at eq1
      nlinarith
    have hy14 : (y + 1) ∣ 5 := by
      use (z + 1)
      all_goals nlinarith [eq8]
    have hy15 : (y + 1) ≤ 5 := by
      exact Int.le_of_dvd (by norm_num) hy14
    have hy16 : (y + 1) ≥ 2 := by
      omega
    interval_cases h55 : (y + 1) <;> try { 
      omega
    } <;> try { tauto } <;> try { linarith }
  · -- x +1 =455
    have eq9 : (y + 1) * (z + 1) = 1 := by
      rw [show (x + 1 : ℤ) = 455 by linarith [h5]] at eq1
      nlinarith
    have eq14 : (y + 1) ≤ 1 := by
      nlinarith
    nlinarith