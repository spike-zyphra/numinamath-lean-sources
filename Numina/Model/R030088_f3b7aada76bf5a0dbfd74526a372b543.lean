import Mathlib

theorem number_theory_57807 (a b c : ℤ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : 0 < c) :
    4 ∣ a^2 + b^2 + c^2 ↔ Even a ∧ Even b ∧ Even c := by
  constructor
  · -- Forward direction: if 4 divides a^2 + b^2 + c^2 then a, b, c are even
    intro h
    have h2 : a % 2 = 0 := by
      by_contra h2
      push_neg at h2
      have ha1 : a % 2 = 1 := by omega
      have h3 : a % 4 = 1 ∨ a % 4 = 3 := by omega
      have h4 : a^2 % 4 = 1 := by
        rcases h3 with (h3 | h3)
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h3]
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h3]
      have h5 : (a^2 + b^2 + c^2) % 4 = 0 := by
        omega
      have h5' : (b^2 + c^2) % 4 = 3 := by 
        omega
      have h6 : b^2 % 4 = 0 ∨ b^2 % 4 = 1 := by 
        have h1 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
        rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      have h7 : c^2 % 4 = 0 ∨ c^2 % 4 = 1 := by 
        have h1 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega
        rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      omega
    have h4 : b % 2 = 0 := by
      by_contra h4
      push_neg at h4
      have hb1 : b % 2 = 1 := by omega
      have h5 : b % 4 = 1 ∨ b % 4 = 3 := by omega
      have h6 : b^2 % 4 = 1 := by
        rcases h5 with (h5 | h5)
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h5]
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h5]
      have h5 : (a^2 + b^2 + c^2) % 4 = 0 := by
        omega
      have h5' : (a^2 + c^2) % 4 = 3 := by 
        omega
      have h6 : a^2 % 4 = 0 ∨ a^2 % 4 = 1 := by 
        have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
        rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      have h7 : c^2 % 4 = 0 ∨ c^2 % 4 = 1 := by 
        have h1 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega
        rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      omega
    have h3 : c % 2 = 0 := by
      by_contra h3
      push_neg at h3
      have hc1 : c % 2 = 1 := by omega
      have h4 : c % 4 = 1 ∨ c % 4 = 3 := by omega
      have h5 : c^2 % 4 = 1 := by
        rcases h4 with (h4 | h4)
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h4]
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h4]
      have h5 : (a^2 + b^2 + c^2) % 4 = 0 := by
        omega
      have h5' : (a^2 + b^2) % 4 = 3 := by 
        omega
      have h6 : a^2 % 4 = 0 ∨ a^2 % 4 = 1 := by 
        have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
        rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      have h7 : b^2 % 4 = 0 ∨ b^2 % 4 = 1 := by 
        have h1 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
        rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1]
      omega
    have ha' : Even a := by
      refine' ⟨a / 2, by omega⟩
    have hb' : Even b := by
      refine' ⟨b / 2, by omega⟩
    have hc' : Even c := by
      refine' ⟨c / 2, by omega⟩
    exact ⟨ha', hb', hc'⟩
  · -- Backward implication: if a, b, c are even then 4 divides a^2 + b^2 + c^2
    rintro ⟨ha, hb, hc⟩
    have h2 : a % 2 = 0 := by
      obtain ⟨k, hk⟩ := ha
      omega
    have h4 : b % 2 = 0 := by
      obtain ⟨k, hk⟩ := hb
      omega
    have h3 : c % 2 = 0 := by
      obtain ⟨k, hk⟩ := hc
      omega
    have h1 : a^2 % 4 = 0 := by
      have ha2 : a % 4 = 0 ∨ a % 4 = 2 := by
        omega
      rcases ha2 with (h | h)
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h]
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h]
    have h2 : b^2 % 4 = 0 := by
      have hb2 : b % 4 = 0 ∨ b % 4 = 2 := by
        omega
      rcases hb2 with (h | h)
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h]
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h]
    have h3 : c^2 % 4 = 0 := by
      have hc2 : c % 4 = 0 ∨ c % 4 = 2 := by
        omega
      rcases hc2 with (h | h)
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h]
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h]
    omega