import Mathlib

theorem number_theory_297044 : ((⌊Real.sqrt 2013⌋ + ⌊Real.sqrt 2014⌋ + ⌊Real.sqrt 2015⌋ + ⌊Real.sqrt 2016⌋) / ((⌊Real.sqrt 2014⌋ * ⌊Real.sqrt 2015⌋))) = 1 / 11 := by
  have h1 : ⌊Real.sqrt 2013⌋ = 44 := by
    have h2 : 44 < Real.sqrt 2013 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h3 : Real.sqrt 2013 < 45 := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> (try linarith)
  have h14 : ⌊Real.sqrt 2014⌋ = 44 := by
    have h2 : 44 < Real.sqrt 2014 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h3 : Real.sqrt 2014 < 45 := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> (try linarith)
  have h15 : ⌊Real.sqrt 2015⌋ = 44 := by
    have h2 : 44 < Real.sqrt 2015 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h3 : Real.sqrt 2015 < 45 := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> (try linarith)
  have h16 : ⌊Real.sqrt 2016⌋ = 44 := by
    have h2 : 44 < Real.sqrt 2016 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h3 : Real.sqrt 2016 < 45 := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> (try linarith)
  simp [h1, h14, h15, h16]
  all_goals norm_num