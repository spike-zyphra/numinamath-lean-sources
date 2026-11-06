import Mathlib

theorem number_theory_4945_1
    (a b : ℤ)
    (ha : a % 2 = 0) (hb : b % 2 = 0) :
    (a + b) % 2 = 0 := by
  -- the sum of two even integers is even
  simp [Int.add_emod, ha, hb]


theorem number_theory_4945_2
    (a b : ℤ)
    (ha : a % 2 ≠ 0) (hb : b % 2 ≠ 0) :
    (a + b) % 2 = 0 := by
  -- the sum of two odd integers is even
  simp only [Int.emod_two_ne_zero] at ha hb
  simp [Int.add_emod, ha, hb]


theorem number_theory_4945_3
    (a b : ℤ)
    (ha : a % 2 ≠ 0) (hb : b % 2 = 0) :
    (a + b) % 2 ≠ 0 := by 
  -- the sum of an odd and even integer is odd
  have ha1 : a % 2 = 1 := by 
    omega 
  have h : (a + b) % 2 = 1 := by
    have h1 : a % 2 = 1 := ha1 
    have h2 : b % 2 = 0 := hb 
    omega 
  intro h'
  -- Now (a + b) % 2 = 0 contradicts our earlier conclusion
  omega 
  all_goals 
    simp [Int.add_emod, ha1, hb] at h' 
    all_goals omega