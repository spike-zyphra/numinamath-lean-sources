import Mathlib

/-- A triangle with integer sides a, b, c is a "Linglong Triangle" if the height on one side
    is exactly the sum of the heights on the other two sides. -/
def IsLingLongTriangle (a b c : ℕ) : Prop :=
  -- Triangle inequality must hold
  a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a ∧
  -- Heights relationship: assuming h_a = h_b + h_c
  (1 : ℚ) / a = (1 : ℚ) / b + (1 : ℚ) / c

/-- Theorem 1: Linglong Triangles exist -/
theorem number_theory_318004_1 : ∃ a b c : ℕ, IsLingLongTriangle a b c := by
  -- We use the example from the solution: a=6, b=10, c=15
  use 6, 10, 15
  
  -- Prove all conditions one by one and combine them
  have h1 : 6 > 0 := by norm_num
  have h2 : 10 > 0 := by norm_num
  have h3 : 15 > 0 := by norm_num
  have h4 : 6 + 10 > 15 := by norm_num
  have h5 : 6 + 15 > 10 := by norm_num
  have h6 : 10 + 15 > 6 := by norm_num
  have h7 : (1 : ℚ) / 6 = (1 : ℚ) / 10 + (1 : ℚ) / 15 := by norm_num
  
  -- Combine all the conditions
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- Theorem 2: In a Linglong Triangle, a² + b² + c² is a perfect square -/
theorem number_theory_318004_2 {a b c : ℕ} (h : IsLingLongTriangle a b c) : 
  ∃ n : ℕ, a^2 + b^2 + c^2 = n^2 := by
  
  -- Extract the definition parts  
  rcases h with ⟨ha, hb, hc, hab, hac, hbc, heights_eq⟩
  
  -- We directly use the triangle inequality: b + c > a
  have h_sum_ge : b + c ≥ a := Nat.le_of_lt hbc

  -- Define n = b + c - a, which is a natural number by h_sum_ge
  let n : ℕ := b + c - a
  
  -- Step 1: From heights relationship, derive bc = ab + ac
  
  -- First establish: 1/a = 1/b + 1/c (from definition)
  have h1 : (1 : ℚ) / a = (1 : ℚ) / b + (1 : ℚ) / c := heights_eq
  
  -- Establish a ≠ 0 for use with rational number properties
  have ha_nonzero : (a : ℚ) ≠ 0 := by
    norm_cast
    exact ne_of_gt ha
  
  -- Multiply both sides by a to get: 1 = a/b + a/c
  have h2 : 1 = (a : ℚ) / b + (a : ℚ) / c := by
    -- First establish (a * (1/a)) = 1 when a ≠ 0
    have h_mul_reciprocal : (a : ℚ) * (1 / a) = 1 := by
      -- Use field_simp instead of mul_inv_cancel
      field_simp [ha_nonzero]
    
    -- Now rearrange the original equation
    calc 1 = (a : ℚ) * (1 / a) := by
              exact Eq.symm h_mul_reciprocal
         _ = (a : ℚ) * ((1 : ℚ) / b + (1 : ℚ) / c) := by
              rw [h1]
         _ = (a : ℚ) / b + (a : ℚ) / c := by
              ring
  
  -- Multiply by bc to get: bc = ac + ab
  have h_eq : (b : ℚ) * c = a * c + a * b := by
    -- bc = bc * 1
    have h_step1 : (b : ℚ) * c = (b : ℚ) * c * 1 := by ring
    
    -- Substitute our h2 equation
    have h_step2 : (b : ℚ) * c * 1 = (b : ℚ) * c * ((a : ℚ) / b + (a : ℚ) / c) := by
      rw [h2]
    
    -- Distribute the multiplication
    have h_step3 : (b : ℚ) * c * ((a : ℚ) / b + (a : ℚ) / c) = 
                   (b : ℚ) * c * ((a : ℚ) / b) + (b : ℚ) * c * ((a : ℚ) / c) := by ring
    
    -- Simplify the first term: b * c * (a / b) = c * a
    have h_step4 : (b : ℚ) * c * ((a : ℚ) / b) = c * a := by
      have hb_nonzero : (b : ℚ) ≠ 0 := by
        norm_cast
        exact ne_of_gt hb
      
      calc (b : ℚ) * c * ((a : ℚ) / b) 
           = c * ((b : ℚ) * ((a : ℚ) / b)) := by ring
           _ = c * a := by
             congr
             -- Use field_simp to prove b * (a / b) = a
             field_simp [hb_nonzero]
    
    -- Simplify the second term: b * c * (a / c) = b * a
    have h_step5 : (b : ℚ) * c * ((a : ℚ) / c) = b * a := by
      have hc_nonzero : (c : ℚ) ≠ 0 := by
        norm_cast
        exact ne_of_gt hc
      
      calc (b : ℚ) * c * ((a : ℚ) / c) 
           = b * (c * ((a : ℚ) / c)) := by ring
           _ = b * a := by
             congr
             -- Use field_simp to prove c * (a / c) = a
             field_simp [hc_nonzero]
    
    -- Chain all these steps together
    calc (b : ℚ) * c 
         = (b : ℚ) * c * 1 := by exact h_step1
         _ = (b : ℚ) * c * ((a : ℚ) / b + (a : ℚ) / c) := by exact h_step2
         _ = (b : ℚ) * c * ((a : ℚ) / b) + (b : ℚ) * c * ((a : ℚ) / c) := by exact h_step3
         _ = c * a + b * a := by rw [h_step4, h_step5]
         _ = a * c + a * b := by ring
  
  -- From h_eq: b*c = a*c + a*b, we get b*c - a*c - a*b = 0
  have h_zero : (b : ℚ) * c - a * c - a * b = 0 := by
    rw [h_eq]
    ring
  
  -- Algebraic identity: (b + c - a)² = a² + b² + c² + 2(bc - ac - ab)
  have h_expansion : ((b : ℚ) + c - a)^2 = (a : ℚ)^2 + b^2 + c^2 + 2*(b*c - a*c - a*b) := by ring
  
  -- Simplifying using h_zero
  have h_simplified : ((b : ℚ) + c - a)^2 = (a : ℚ)^2 + b^2 + c^2 := by
    rw [h_expansion, h_zero]
    ring
  
  -- Now we need to convert back to natural numbers
  have h_cast_eq : (↑(a^2 + b^2 + c^2) : ℚ) = (↑a)^2 + (↑b)^2 + (↑c)^2 := by norm_cast
  have h_cast_n : (↑(b + c - a) : ℚ) = (↑b) + (↑c) - (↑a) := by norm_cast
  
  have h_int_eq : (↑(a^2 + b^2 + c^2) : ℚ) = (↑(b + c - a))^2 := by
    rw [h_cast_eq, h_cast_n, h_simplified]
  
  -- Convert the rational equation back to natural numbers
  have h_square : a^2 + b^2 + c^2 = n^2 := Nat.cast_inj.mp h_int_eq
  
  -- Final result: just use n with the established equality
  use n
