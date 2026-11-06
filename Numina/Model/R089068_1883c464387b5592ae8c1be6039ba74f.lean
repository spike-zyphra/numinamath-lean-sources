import Mathlib

theorem number_theory_198133 {a b : ℤ} (h : 3 ∣ a^2 + b^2) :
    3 ∣ a ∧ 3 ∣ b := by
  have h1 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by 
    omega
  have h2 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by
    omega
  rcases h1 with (h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) <;> ( 
    simp [Int.dvd_iff_emod_eq_zero, Int.add_emod, pow_two, Int.mul_emod, h1, h2] at h ⊢
    <;> try { 
      tauto
    }
    <;> try { 
      omega 
      <;> try { tauto } 
    }
    <;> try { 
      constructor <;> try { 
        omega 
      } <;> try { 
        tauto 
      } 
    }
  )