import Mathlib

theorem number_theory_4781 [Fact (Nat.Prime 7)] : 8*9*10*11*12*13 = (6 : ZMod 7) := by 
  have h1 : (8 * 9 * 10 * 11 * 12 * 13) % 7 = 6 := by 
    norm_num
  have h5 : (8 * 9 * 10 * 11 * 12 * 13 : ℕ) = (176502 * 7 + 6 : ℕ) := by
    norm_num 
  have h6 : (8 * 9 * 10 * 11 * 12 * 13) % 7 = 6 := by 
    omega 
  have h7 : (8 * 9 * 10 * 11 * 12 * 13 : ZMod 7) = (6 : ZMod 7) := by 
    simp [h5, h6, ZMod]
    <;> try { 
      native_decide 
    }
  exact_mod_cast h7