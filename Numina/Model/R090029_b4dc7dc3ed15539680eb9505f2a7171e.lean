import Mathlib

theorem number_theory_190506 (h : 1 ≤ P ∧ P ≤ 9) (h' : 0 ≤ B ∧ B ≤ 9)
    (h'' : 0 ≤ Γ ∧ Γ ≤ 9) (h''' : P ≠ B) (h'''' : P ≠ Γ) (h''''' : B ≠ Γ)
    (h'''''' : 100 * P + 10 * B + Γ = (P + B + Γ) * (P + B + Γ + 1)) :
    156 = 100 * P + 10 * B + Γ := by 
  have hP1 : 1 ≤ P := h.1 
  have hP2 : P ≤ 9 := h.2 
  have hB1 : 0 ≤ B := h'.1 
  have hB2 : B ≤ 9 := h'.2 
  have hG1 : 0 ≤ Γ := h''.1 
  have hG2 : Γ ≤ 9 := h''.2 
  interval_cases P <;> interval_cases B <;> interval_cases Γ 
    <;> norm_num at h'''''' 
      <;> try { 
        omega 
      }
    <;> try { 
      norm_num 
      <;> try { 
        omega 
      }
    }
    <;> try { 
      omega 
    }