import Mathlib

theorem number_theory_46299 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ¬(IsSquare (2 * a ^ 2 + b ^ 2 + 3) ∧ IsSquare (2 * b ^ 2 + c ^ 2 + 3) ∧ IsSquare (2 * c ^ 2 + a ^ 2 + 3)) := by
  rintro ⟨h₁, h₂, h₃⟩
  
  -- lemma of mod8.
  have hmod8 (n : ℤ) (hnsq : IsSquare n) : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 4 := by 
    rcases hnsq with ⟨x, hx⟩
    have hx1 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
      omega
    rcases hx1 with (hx1 | hx1 | hx1 | hx1 | hx1 | hx1 | hx1 | hx1) <;> 
    norm_num [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, hx, hx1]
  
  have h₁' : (2 * a ^ 2 + b ^ 2 + 3) % 8 = 0 ∨ (2 * a ^ 2 + b ^ 2 + 3) % 8 = 1 ∨ (2 * a ^ 2 + b ^ 2 + 3) % 8 = 4 := hmod8 (2 * a ^ 2 + b ^ 2 + 3) h₁
  have h₂' : (2 * b ^ 2 + c ^ 2 + 3) % 8 = 0 ∨ (2 * b ^ 2 + c ^ 2 + 3) % 8 = 1 ∨ (2 * b ^ 2 + c ^ 2 + 3) % 8 = 4 := hmod8 (2 * b ^ 2 + c ^ 2 + 3) h₂
  have h₃' : (2 * c ^ 2 + a ^ 2 + 3) % 8 = 0 ∨ (2 * c ^ 2 + a ^ 2 + 3) % 8 = 1 ∨ (2 * c ^ 2 + a ^ 2 + 3) % 8 = 4 := hmod8 (2 * c ^ 2 + a ^ 2 + 3) h₃
  
  have h1 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
    omega
  
  have h2 : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
    omega
  
  have h3 : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by
    omega
  
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> 
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> 
        norm_num [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h1, h2, h3] at h₁' h₂' h₃' <;> 
          omega