import Mathlib

/- PROBLEM: Josh and Mike live 13 miles apart. Yesterday, Josh started to ride his bicycle toward Mike's house. A little later Mike started to ride his bicycle toward Josh's house. When they met, Josh had ridden for twice the length of time as Mike and at four-fifths of Mike's rate. How many miles had Mike ridden when they met? -/
theorem algebra_97295 
  (j m : ℝ) 
  (hj : j > 0) 
  (hm : m > 0) 
  (hj1 : j * 5 = m * 8) 
  (hj2 : j + m = 13) : 
  m = 5 := 
by {
  have : m = 13 - (m*8)/5 := by {
    calc m = j + m - j := by ring
         _ = 13 - j := by rw [hj2]
         _ = 13 - (j*5)/5 := by ring
         _ = 13 - (m*8)/5 := by rw [hj1]
  }

  field_simp at this
  ring_nf at this
  calc m = (m * 13) / 13 := by norm_num
         _ = (m * 5 + m * 8) / 13 := by ring
         _ = (65 - m * 8 + m * 8) / 13 := by rw [this]
         _ = 65 / 13 := by ring
         _ = 5 := by norm_num
}