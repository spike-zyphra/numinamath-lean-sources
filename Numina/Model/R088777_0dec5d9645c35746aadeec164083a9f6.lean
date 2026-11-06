import Mathlib

theorem number_theory_2841 :
    ∀ a b c : ℤ, Even (|a + b| + |b - c| + |a - c|) := by
  intro a b c
  have h1 : (|a + b| + |b - c| + |a - c|) % 2 = 0 := by
    have h2 : |a + b| % 2 = (a + b) % 2 := by 
      cases' abs_cases (a + b) with h h 
      · omega 
      · omega 
    have h3 : |b - c| % 2 = (b - c) % 2 := by 
      cases' abs_cases (b - c) with h h 
      · omega 
      · omega 
    have h4 : |a - c| % 2 = (a - c) % 2 := by 
      cases' abs_cases (a - c) with h h 
      · omega 
      · omega 
    simp [Int.add_emod, h2, h3, h4]
    -- show that total sum is 0 mod 2
    -- we compute total expression
    -- (a + b) + (b - c) + (a - c) = 2a + 2b - 2c = 2*(a + b - c) 
    -- which is even
    ring_nf 
    <;> omega 
  exact ⟨(|a + b| + |b - c| + |a - c|) / 2, by omega⟩