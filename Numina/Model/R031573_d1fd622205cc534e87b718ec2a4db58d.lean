import Mathlib

open Real Set
open scoped BigOperators


theorem algebra_128226 {f : ℝ → ℝ} (h : ∀ x, f (2 + x) = f (2 - x))(x y z w : ℝ)
(hroots : x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w ∧
f x = 0 ∧ f y = 0 ∧ f z = 0 ∧ f w = 0)(hrootunique : ∀ r, f r = 0 → r = x ∨ r = y ∨ r = z ∨ r = w) :
x + y + z + w = 8 := by
  obtain ⟨hxy, hxz, hxw, hyz, hyw, hzw, hfx, hfy, hfz, hfw⟩ := hroots
  have h1 : ∀ r, f r = 0 → f (4 - r) = 0 := by
    intro r hr
    have eq1 := h (2 - r)
    have eq2 : 2 + (2 - r) = 4 - r := by ring
    have eq3 : 2 - (2 - r) = r := by ring
    rw [eq2, eq3] at eq1
    have eq4 : f (4 - r) = f r := by linarith [eq1]
    have eq5 : f r = 0 := by linarith [hr]
    have eq6 : f (4 - r) = 0 := by linarith [eq4, eq5]
    assumption
  have hx' : f (4 - x) = 0 := h1 x hfx
  have hy' : f (4 - y) = 0 := h1 y hfy
  have hz' : f (4 - z) = 0 := h1 z hfz
  have hw' : f (4 - w) = 0 := h1 w hfw
  have h2 : 4 - x = x ∨ 4 - x = y ∨ 4 - x = z ∨ 4 - x = w := by 
    apply hrootunique (4 - x) hx'
  have h3 : 4 - y = x ∨ 4 - y = y ∨ 4 - y = z ∨ 4 - y = w := by
    apply hrootunique (4 - y) hy'
  have h4 : 4 - z = x ∨ 4 - z = y ∨ 4 - z = z ∨ 4 - z = w := by
    apply hrootunique (4 - z) hz'
  have h5 : 4 - w = x ∨ 4 - w = y ∨ 4 - w = z ∨ 4 - w = w := by
    apply hrootunique (4 - w) hw'
  rcases h2 with h2 | h2 | h2 | h2 <;> rcases h3 with h3 | h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4 | h4 <;> rcases h5 with h5 | h5 | h5 | h5 <;> 
    try { 
      linarith 
    }
  all_goals
    try { 
      have : False := by 
        try { 
          apply hxy 
          linarith 
        } 
        <;> try { 
          apply hxz 
          linarith 
        } 
        <;> try { 
          apply hxw 
          linarith 
        }
        <;> try { 
          apply hyz 
          linarith 
        }
        <;> try { 
          apply hyw 
          linarith 
        }
        <;> try { 
          apply hzw 
          linarith 
        }
      contradiction 
    }
  all_goals 
    try { 
      linarith 
    }