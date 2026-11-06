import Mathlib

theorem algebra_7439 (x : ℝ) : 7 * Int.fract x = x + Int.floor x → x ≤ 8 / 3 := by 
  intro h
  have h1 : Int.fract x = x - Int.floor x := by 
    rw [Int.fract]
    <;> simp
  rw [h1] at h
  have h2 : (Int.floor x : ℝ) ≤ x := by 
    exact Int.floor_le x
  have h3 : x < (Int.floor x + 1 : ℝ) := by
    exact Int.lt_floor_add_one x
  have h4 : (Int.floor x : ℝ) ≤ x := by 
    exact Int.floor_le x
  have h7 : Int.floor x ≤ (2 : Int) := by
    by_contra h8
    push_neg at h8
    have h8' : Int.floor x ≥ (3 : Int) := by
      omega
    have h8 : (Int.floor x : ℝ) ≥ (3 : ℝ) := by
      exact_mod_cast h8'
    have h9 : 6 * x = 8 * (Int.floor x : ℝ) := by
      nlinarith 
    nlinarith [Int.floor_le x, Int.lt_floor_add_one x, show (Int.floor x : ℝ) ≤ x by exact Int.floor_le x, show x < (Int.floor x + 1 : ℝ) by exact Int.lt_floor_add_one x]
  have h8 : (Int.floor x : ℝ) ≤ (2 : ℝ) := by 
    exact_mod_cast h7
  nlinarith [Int.floor_le x, Int.lt_floor_add_one x, h7, show (Int.floor x : ℝ) ≤ x by exact Int.floor_le x, show x < (Int.floor x + 1 : ℝ) by exact Int.lt_floor_add_one x]