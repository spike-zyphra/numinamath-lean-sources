import Mathlib

open Real
open scoped BigOperators

theorem inequalities_228138 (a b c : ℝ) (h₀ : 0 < a) (h₁ : 0 < b) (h₂ : 0 < c)
  (h₃ : a + b > c) (h₄ : a + c > b) (h₅ : b + c > a) (s : ℝ)
  (hs : s = (1/2) * a * b * sin (arccos ((a^2 + b^2 - c^2)/(2*a*b)))) :
  a^2 + b^2 + c^2 ≥ 4*sqrt 3 * s := by
    have h1 : sin (arccos ((a^2 + b^2 - c^2) / (2 * a * b))) = Real.sqrt (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2) := by
      rw [sin_arccos]
    rw [h1] at hs
    have h7 : s = (1/2) * a * b * Real.sqrt (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2) := by
      linarith 
    rw [h7]
    have h_nonneg : 0 ≤ 1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2 := by
      have h6 : 0 < a * b := mul_pos h₀ h₁ 
      have h96 : -1 ≤ (a^2 + b^2 - c^2) / (2 * a * b) := by 
        have h95 : -1 ≤ (a^2 + b^2 - c^2) / (2 * a * b) := by
          apply (le_div_iff₀ (by positivity)).mpr 
          nlinarith [sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a), 
            mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂]
        linarith 
      have h97 : (a^2 + b^2 - c^2) / (2 * a * b) ≤ 1 := by 
        have h98 : (a^2 + b^2 - c^2) / (2 * a * b) ≤ 1 := by 
          apply (div_le_iff₀ (by positivity)).mpr 
          nlinarith [sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a), 
            mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂]
        linarith 
      nlinarith [sq_nonneg ((a^2 + b^2 - c^2) / (2 * a * b)), h96, h97]
    
    have h6 : (a^2 + b^2 + c^2) ^ 2 ≥ 12 * a^2 * b^2 * (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2) := by
      have h_eq2 : 12 * a^2 * b^2 * (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2) = 3 * (4 * a^2 * b^2 - (a^2 + b^2 - c^2)^2) := by 
        field_simp [show 0 < a * b by positivity]
        <;> ring_nf 
        <;> field_simp [show 0 < a * b by positivity]
        <;> ring_nf 
      rw [h_eq2] 
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂,
          mul_pos (show 0 < a + b - c by linarith) (show 0 < a + c - b by linarith), 
          mul_pos (show 0 < a + c - b by linarith) (show 0 < b + c - a by linarith), 
          mul_pos (show 0 < a + b - c by linarith) (show 0 < b + c - a by linarith),
          h_nonneg
        ]
    
    have h7 : a ^ 2 + b ^ 2 + c ^ 2 ≥ 0 := by positivity 
    have h8 : (4 * Real.sqrt 3 * ((1 / 2) * a * b * Real.sqrt (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2))) ^ 2 ≤ (a^2 + b^2 + c^2) ^ 2 := by 
      have eq : (4 * Real.sqrt 3 * ((1 / 2) * a * b * Real.sqrt (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2))) ^ 2 = 12 * a^2 * b^2 * (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2) := by 
        calc 
          (4 * Real.sqrt 3 * ((1 / 2) * a * b * Real.sqrt (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2))) ^ 2 
              = 16 * (Real.sqrt 3)^2 * ((1 / 2) * a * b * Real.sqrt (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2))^2 := by ring_nf 
          _ = 16 * (Real.sqrt 3)^2 * (((1 / 4) * a^2 * b^2) * (Real.sqrt (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2))^2) := by 
            ring_nf 
          _ = 16 * (Real.sqrt 3)^2 * (((1 / 4) * a^2 * b^2) * (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2)) := by 
            rw [Real.sq_sqrt h_nonneg]
            <;> ring_nf 
          _ = 12 * a^2 * b^2 * (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2) := by 
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      nlinarith [h6, eq, Real.sqrt_nonneg 3, Real.sqrt_nonneg (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2)]
    
    have h9 : 4 * Real.sqrt 3 * ((1 / 2) * a * b * Real.sqrt (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2)) ≥ 0 := by 
      positivity 
    
    have h10 : a^2 + b^2 + c^2 ≥ 4 * Real.sqrt 3 * ((1 / 2) * a * b * Real.sqrt (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2)) := by 
      nlinarith [sq_nonneg (a^2 + b^2 + c^2 - 4 * Real.sqrt 3 * ((1 / 2) * a * b * Real.sqrt (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2))), 
        Real.sqrt_nonneg 3, 
        Real.sqrt_nonneg (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2), 
        mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2)), 
        sq_nonneg (a^2 + b^2 + c^2 + 4 * Real.sqrt 3 * ((1 / 2) * a * b * Real.sqrt (1 - ((a^2 + b^2 - c^2) / (2 * a * b))^2))), 
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
        Real.sq_sqrt h_nonneg
      ]
    
    exact h10