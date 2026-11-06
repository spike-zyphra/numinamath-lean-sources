import Mathlib

theorem algebra_199349 (c : ℝ) (f : ℕ → ℝ) (hf1 : f 1 = 0)
    (hfn : ∀ n > 0, f (n + 1) = c * (f n)^3 + 1 - c) :
    (∀ n > 0, f n ∈ Set.Icc 0 1) ↔ c ∈ Set.Icc 0 1 := by 
  constructor
  · -- Forward direction: if $f(n) \in [0,1]$ for all $n > 0$, prove $c \in [0,1]$
    intro hf
    have h2 := hf 2 (by norm_num)
    have eq1 : f 2 = 1 - c := by
      specialize hfn 1 (by norm_num)
      simp [hf1] at hfn 
      linarith 
    rw [eq1] at h2 
    have h21 := h2.1 
    have h22 := h2.2 
    constructor <;> nlinarith 
  · -- Reverse direction: if $c \in [0,1]$, prove $f(n) \in [0,1]$ for all $n > 0$
    intro hc
    rcases hc with ⟨hc1, hc2⟩
    intro n hn 
    have h_ind : ∀ n > 0, f n ∈ Set.Icc 0 1 := by 
      intro n hn 
      induction n with 
      | zero =>
        exfalso 
        exact Nat.lt_irrefl 0 hn 
      | succ n ih =>
        cases n with 
        | zero =>
          have h1 : f 1 ∈ Set.Icc 0 1 := by 
            rw [hf1]
            exact ⟨by norm_num, by norm_num⟩ 
          simpa using h1 
        | succ n =>
          have h2 : f (n + 1 + 1) = c * (f (n + 1)) ^ 3 + 1 - c := hfn (n + 1) (by omega)
          have ih' : f (n + 1) ∈ Set.Icc 0 1 := ih (by omega)
          rw [h2]
          rcases ih' with ⟨fhn1, fhn2⟩
          have h4 : (f (n + 1)) ^ 3 ≥ 0 := by 
            nlinarith [sq_nonneg (f (n + 1)), sq_nonneg (f (n + 1) - 1)]
          have h5 : (f (n + 1)) ^ 3 ≤ 1 := by 
            nlinarith [sq_nonneg (f (n + 1)), sq_nonneg (f (n + 1) - 1)]
          constructor <;> nlinarith 
    specialize h_ind n hn 
    simpa using h_ind