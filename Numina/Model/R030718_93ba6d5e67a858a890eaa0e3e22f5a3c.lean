import Mathlib

theorem algebra_177259 {V W : ℕ} (hV : V ∈ Finset.Icc 10 99) (hW : W ∈ Finset.Icc 10 99) (hlt : W ≤ V)
    (quot : (1000 * V + W) / (1000 * W + 10 * V) = 2)
    (rmd : (1000 * V + W) % (1000 * W + 10 * V) = 590) (h : 2 * V + 3 * W = 72) :
    V = 21 ∧ W = 10 := by 
  rw [Finset.mem_Icc] at hV hW
  rcases hV with ⟨h11, h12⟩
  rcases hW with ⟨h21, h22⟩
  have h1 : V ≥ 10 := by linarith
  have h2 : V ≤ 99 := by linarith
  have h3 : W ≥ 10 := by linarith
  have h4 : W ≤ 99 := by linarith

  have h5 : (1000 * W + 10 * V) ≠ 0 := by 
    omega
  have h6 : 1000 * W + 10 * V > 0 := by 
    omega

  have h7 : (1000 * V + W) = 2 * (1000 * W + 10 * V) + 590 := by
    have h8 : (1000 * V + W) = (1000 * W + 10 * V) * ((1000 * V + W) / (1000 * W + 10 * V)) + ((1000 * V + W) % (1000 * W + 10 * V)) := by
      rw [Nat.div_add_mod (1000 * V + W) (1000 * W + 10 * V)]
    
    have h9 : (1000 * V + W) / (1000 * W + 10 * V) = 2 := by 
      exact quot
    have h10 : (1000 * V + W) % (1000 * W + 10 * V) = 590 := by 
      exact rmd
    rw [h9, h10] at h8
    linarith
  
  interval_cases V <;> omega