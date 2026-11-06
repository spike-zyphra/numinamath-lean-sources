import Mathlib

theorem number_theory_123634 :
    ¬∃ f : ℕ → ℕ, ∀ n, f (f n) = n + 1 := by
  rintro ⟨f, hf⟩
  have h1 : ∀ n, f (n + 1) = f n + 1 := by
    intro n
    have h2 : f (f n) = n + 1 := hf n
    have h3 : f (f (f n)) = f n + 1 := by 
      specialize hf (f n)
      simpa using hf 
    have h4 : f (n + 1) = f (f (f n)) := by
      have h2f : f (f n) = n + 1 := hf n 
      rw [←h2f]
      all_goals simpa
    linarith [h3, h4]
  have h5 : ∀ n, f n = f 0 + n := by
    intro n 
    induction n with 
    | zero =>
      simp 
    | succ n ih =>
      have h6 : f (n + 1) = f n + 1 := h1 n
      rw [h6]
      omega
  have h6 : f (f 0) = 1 := by
    specialize hf 0
    simpa using hf 
  have h7 : f (f 0) = f 0 + f 0 := by 
    specialize h5 (f 0)
    simpa using h5 
  omega