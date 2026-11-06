import Mathlib

theorem number_theory_115912 (a b c d e f : ℕ) (ha : a.Prime) (hb : b.Prime)
    (hc : c.Prime) (hd : d.Prime) (he : e.Prime) (hf : f.Prime)
    (hsum : a + b + c + d + e + f = 20) (h1 : a + b + c = d + e + f)
    (h2 : b + c + d = a + e + f) (h3 : c + d + e = a + b + f)
    (h4 : d + e + f = a + b + c) :
    a * b * c * d * e * f = 900 := by
  have h5 : d = a := by 
    omega
  have h6 : e = b := by 
    omega
  have h7 : f = c := by 
    omega
  have h8 : a + b + c = 10 := by 
    omega
  have h9 : a * b * c = 30 := by
    -- rewrite the d, e, f with a, b, c.
    have h10 : a ≤ 10 := by 
      omega
    have h11 : b ≤ 10 := by 
      omega
    have h12 : c ≤ 10 := by 
      omega
    interval_cases a <;> interval_cases b <;> interval_cases c
    <;> norm_num at h8 ha hb hc ⊢ 
    <;> omega
  -- substituting the rewritten variables.
  calc
    a * b * c * d * e * f = a * b * c * a * b * c := by rw [h5, h6, h7]
    _ = (a * b * c) ^ 2 := by ring
    _ = 30 ^ 2 := by rw [h9]
    _ = 900 := by norm_num