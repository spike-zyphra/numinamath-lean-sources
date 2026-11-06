import Mathlib

theorem number_theory_170890 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) (h₁ : n % 10 = n / 100 % 10)
    (h₂ : (1000 * (n % 10) + 100 * ((n / 10) % 10) + 10 * ((n / 100) % 10) + (n / 1000)) - n = 7812) :
    n = 1979 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h3, h4⟩
  -- Extract digits of n
  have h6 : n % 1000 < 1000 := by
    omega
  have h8 : n % 100 = n % 100 := rfl
  have h9 : n % 1000 = 100 * (n / 100 % 10) + (n % 100) := by
    omega
  have h10 : n % 100 = 10 * (n / 10 % 10) + (n % 10) := by
    omega
  have eq1 : n % 1000 = 100 * (n / 100 % 10) + (10 * (n / 10 % 10) + (n % 10)) := by
    rw [h9, h10]
    all_goals omega
  -- From h₁, we know the units digit equals the hundreds digit
  have h11 : n % 10 = n / 100 % 10 := h₁
  have d1 : n % 10 = n % 10 := by rfl
  have d2 : n / 10 % 10 = n / 10 % 10 := by rfl
  have d3 : n / 100 % 10 = n / 100 % 10 := by rfl
  have d4 : n / 1000 = n / 1000 := by rfl
  have d1_lt : n % 10 < 10 := by 
    omega
  have d2_lt : n / 10 % 10 < 10 := by 
    omega
  have d3_lt : n / 100 % 10 < 10 := by 
    omega
  have d4_lt : n / 1000 < 10 := by 
    omega
  -- Also, the digit must be at most 9 
  have d4_pos : n / 1000 > 0 := by 
    omega
  -- Equation from digits
  have eq2 : n = 1000 * (n / 1000) + 100 * (n / 100 % 10) + 10 * (n / 10 % 10) + (n % 10) := by
    omega
  -- Reversed number expression 
  -- From equation h₂ 
  -- Reversed number = 1000 * units + 100 * tens + 10 * hundreds + thousands 
  -- Reversed number = 1000*(n%10) + 100*((n/10)%10) + 10*((n/100)%10) + n/1000
  -- Substitute from eq1 and eq2, solve using omega.
  omega