import Mathlib

def isClosed (S : Set ℝ) := ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S ∧ a - b ∈ S

theorem algebra_323722 : ¬isClosed {x | ∃ n : ℕ, x = n} := by 
  intro h 
  have h1 : (0 : ℝ) ∈ ( {x | ∃ n : ℕ, x = n} : Set ℝ) := by
    use 0 
    all_goals norm_num 
  have h2 : (1 : ℝ) ∈ ( {x | ∃ n : ℕ, x = n} : Set ℝ) := by
    use 1 
    all_goals norm_num 
  have h3 := h (0 : ℝ) (show (0 : ℝ) ∈ ( {x | ∃ n : ℕ, x = n} : Set ℝ) by 
    exact_mod_cast h1 ) (1 : ℝ) (show (1 : ℝ) ∈ ( {x | ∃ n : ℕ, x = n} : Set ℝ) by 
    exact_mod_cast h2 
  )
  have h5 : (-1 : ℝ) ∈ ( {x | ∃ n : ℕ, x = n} : Set ℝ) := by
    have h6 := h3.right
    simpa using h6 
  rcases h5 with ⟨m, hm⟩ 
  have h7 : (m : ℝ) ≥ (0 : ℝ) := by 
    have h8 : (m : ℕ) ≥ (0 : ℕ) := by linarith 
    exact_mod_cast h8 
  linarith