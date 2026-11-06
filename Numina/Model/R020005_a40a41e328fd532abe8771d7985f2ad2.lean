import Mathlib

theorem number_theory_7231
    (a b c d : ℤ) :
    (8 ∣ a^2 + b^2 + c^2 + d^2) → Even a ∧ Even b ∧ Even c ∧ Even d := by
  intro h
  have h9 : a % 2 = 0 := by
    by_contra h
    push_neg at h
    have ha1 : a % 2 = 1 := by omega
    have h1 : a^2 % 8 = 1 := by
      have h2 : a % 2 = 1 := by omega
      have h3 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
        omega
      rcases h3 with (h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    have h10 : b^2 % 8 = 0 ∨ b^2 % 8 = 1 ∨ b^2 % 8 = 4 := by
      have h1' : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
        omega
      rcases h1' with (h | h | h | h | h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    have h11 : c^2 % 8 = 0 ∨ c^2 % 8 = 1 ∨ c^2 % 8 = 4 := by
      have h1' : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by
        omega
      rcases h1' with (h | h | h | h | h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    have h12 : d^2 % 8 = 0 ∨ d^2 % 8 = 1 ∨ d^2 % 8 = 4 := by
      have h1' : d % 8 = 0 ∨ d % 8 = 1 ∨ d % 8 = 2 ∨ d % 8 = 3 ∨ d % 8 = 4 ∨ d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7 := by
        omega
      rcases h1' with (h | h | h | h | h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    omega
  have h10 : b % 2 = 0 := by
    by_contra h
    push_neg at h
    have hb1 : b % 2 = 1 := by omega
    have h2 : b^2 % 8 = 1 := by
      have h2 : b % 2 = 1 := by omega
      have h3 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by
        omega
      rcases h3 with (h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    have h11 : a^2 % 8 = 0 ∨ a^2 % 8 = 1 ∨ a^2 % 8 = 4 := by
      have h1' : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
        omega
      rcases h1' with (h | h | h | h | h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    have h12 : c^2 % 8 = 0 ∨ c^2 % 8 = 1 ∨ c^2 % 8 = 4 := by
      have h1' : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by
        omega
      rcases h1' with (h | h | h | h | h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    have h13 : d^2 % 8 = 0 ∨ d^2 % 8 = 1 ∨ d^2 % 8 = 4 := by
      have h1' : d % 8 = 0 ∨ d % 8 = 1 ∨ d % 8 = 2 ∨ d % 8 = 3 ∨ d % 8 = 4 ∨ d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7 := by
        omega
      rcases h1' with (h | h | h | h | h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    omega
  have h11 : c % 2 = 0 := by
    by_contra h
    push_neg at h
    have hc1 : c % 2 = 1 := by omega
    have h3 : c^2 % 8 = 1 := by
      have h2 : c % 2 = 1 := by omega
      have h3 : c % 8 = 1 ∨ c % 8 = 3 ∨ c % 8 = 5 ∨ c % 8 = 7 := by
        omega
      rcases h3 with (h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    have h12 : a^2 % 8 = 0 ∨ a^2 % 8 = 1 ∨ a^2 % 8 = 4 := by
      have h1' : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
        omega
      rcases h1' with (h | h | h | h | h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    have h13 : b^2 % 8 = 0 ∨ b^2 % 8 = 1 ∨ b^2 % 8 = 4 := by
      have h1' : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
        omega
      rcases h1' with (h | h | h | h | h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    have h14 : d^2 % 8 = 0 ∨ d^2 % 8 = 1 ∨ d^2 % 8 = 4 := by
      have h1' : d % 8 = 0 ∨ d % 8 = 1 ∨ d % 8 = 2 ∨ d % 8 = 3 ∨ d % 8 = 4 ∨ d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7 := by
        omega
      rcases h1' with (h | h | h | h | h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    omega
  have h12 : d % 2 = 0 := by
    by_contra h
    push_neg at h
    have hd1 : d % 2 = 1 := by omega
    have h4 : d^2 % 8 = 1 := by
      have h2 : d % 2 = 1 := by omega
      have h3 : d % 8 = 1 ∨ d % 8 = 3 ∨ d % 8 = 5 ∨ d % 8 = 7 := by
        omega
      rcases h3 with (h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    have h13 : a^2 % 8 = 0 ∨ a^2 % 8 = 1 ∨ a^2 % 8 = 4 := by
      have h1' : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
        omega
      rcases h1' with (h | h | h | h | h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    have h14 : b^2 % 8 = 0 ∨ b^2 % 8 = 1 ∨ b^2 % 8 = 4 := by
      have h1' : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
        omega
      rcases h1' with (h | h | h | h | h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    have h15 : c^2 % 8 = 0 ∨ c^2 % 8 = 1 ∨ c^2 % 8 = 4 := by
      have h1' : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by
        omega
      rcases h1' with (h | h | h | h | h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.ofNat] <;> try { omega }
    omega
  constructor
  · -- Show that a is even
    exact ⟨a / 2, by omega⟩
  constructor
  · -- Show that b is even
    exact ⟨b / 2, by omega⟩
  constructor
  · -- Show that c is even
    exact ⟨c / 2, by omega⟩
  · -- Show that d is even
    exact ⟨d / 2, by omega⟩