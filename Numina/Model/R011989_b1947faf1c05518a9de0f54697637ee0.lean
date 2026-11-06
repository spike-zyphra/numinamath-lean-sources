import Mathlib

open Real Nat
open scoped BigOperators

theorem algebra_324732 :
  ∃ n : ℕ, ∀ m : ℕ, n < m → (100^(m + 1) / (Nat.factorial (m + 1) : ℝ)) < (100^m / (Nat.factorial m : ℝ)) := by 
  use 100 
  intro m hm
  have h1 : (m : ℝ) > (100 : ℝ) := by 
    exact_mod_cast (show m > 100 by omega)
  have h2 : (Nat.factorial (m + 1) : ℝ) = (Nat.factorial m : ℝ) * (m + 1 : ℝ) := by 
    have h5 : (Nat.factorial (m + 1) : ℝ) = (m + 1 : ℝ) * (Nat.factorial m : ℝ) := by
      have h3 : Nat.factorial (m + 1) = (m + 1) * (Nat.factorial m) := by 
        simp [Nat.factorial]
      have h4 : (Nat.factorial (m + 1) : ℝ) = ((m + 1) * (Nat.factorial m) : ℝ) := by 
        exact_mod_cast h3
      ring_nf at h4 ⊢ 
      <;> try linarith
      <;> try nlinarith
    have h6 : (Nat.factorial (m + 1) : ℝ) = (Nat.factorial m : ℝ) * (m + 1 : ℝ) := by 
      have h7 : (Nat.factorial (m + 1) : ℝ) = (m + 1 : ℝ) * (Nat.factorial m : ℝ) := h5 
      have h8 : (m + 1 : ℝ) * (Nat.factorial m : ℝ) = (Nat.factorial m : ℝ) * (m + 1 : ℝ) := by ring 
      linarith 
    exact_mod_cast h6 
  have h4 : (100 : ℝ) ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) = ( (100 : ℝ) / (m + 1 : ℝ) ) * ( (100 : ℝ) ^ m / (Nat.factorial m : ℝ) ) := by 
    rw [h2]
    field_simp
    <;> ring
  have h5 : ( (100 : ℝ) / (m + 1 : ℝ) ) < 1 := by 
    have h6 : (m + 1 : ℝ) > 100 := by 
      have h1 : (m : ℝ) > (100 : ℝ) := by 
        exact_mod_cast (show m > 100 by omega)
      nlinarith 
    apply (div_lt_iff₀ (by positivity)).mpr 
    nlinarith 
  have h8 : (100 : ℝ) ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) < (100 : ℝ) ^ m / (Nat.factorial m : ℝ) := by 
    rw [h4]
    have h11 : ( (100 : ℝ) / (m + 1 : ℝ) ) < 1 := h5 
    have h12 : ( (100 : ℝ) ^ m / (Nat.factorial m : ℝ) ) > 0 := by 
      positivity 
    nlinarith [show (0 : ℝ) < 1 by norm_num, h11, h12]
  exact h8