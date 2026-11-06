import Mathlib

theorem number_theory_272042 (a : ℕ → ℕ) (_ha : ∀ i ∈ Finset.range 101, a i > 0)
    (h : ∀ i ∈ Finset.range 100, Even (a i) → a (i + 1) = (a i) / 2 + 1)
    (h' : ∀ i ∈ Finset.range 100, Odd (a i) → a (i + 1) = (a i + 1) / 2) :
    a 0 = 16 → a 100 = 2 := by
  intro a0_eq
  have ha1 : a 1 = 9 := by
    specialize h 0 (by simp) (by rw [a0_eq]; decide)
    norm_num [a0_eq] at h ⊢
    omega
  have ha2 : a 2 = 5 := by
    have h1 : a 1 = 9 := ha1
    have h4 : Odd (a 1) := by
      rw [h1]
      decide
    specialize h' 1 (by simp) h4
    norm_num [h1] at h' ⊢
    omega
  have ha3 : a 3 = 3 := by
    have h2 : a 2 = 5 := ha2
    have h4 : Odd (a 2) := by
      rw [h2]
      decide
    specialize h' 2 (by simp) h4
    norm_num [h2] at h' ⊢
    omega
  have ha4 : a 4 = 2 := by
    have h3 : a 3 = 3 := ha3
    have h4 : Odd (a 3) := by
      rw [h3]
      decide
    specialize h' 3 (by simp) h4
    norm_num [h3] at h' ⊢
    omega
  have h100 : ∀ (n : ℕ), n ≤ 96 → a (4 + n) = 2 := by
    intro n hn
    induction n with
    | zero =>
      simp [ha4]
    | succ n ih =>
      have hn : n + 1 ≤ 96 := by omega
      have eq4 : 4 + (n + 1) = (4 + n) + 1 := by ring
      have eq100 : a (4 + (n + 1)) = 2 := by
        have eq4' : a (4 + (n + 1)) = a ((4 + n) + 1) := by
          rw [eq4]
        have he : Even (a (4 + n)) := by
          have h4' : a (4 + n) = 2 := ih (by omega)
          rw [h4'] 
          decide
        have h3 : a ((4 + n) + 1) = a (4 + n) / 2 + 1 := by
          have h4' : a (4 + n) = 2 := ih (by omega)
          have he : Even (a (4 + n)) := by 
            rw [h4']
            decide
          specialize h (4 + n) (by
            have : (4 + n) < 100 := by 
              omega
            simp at *
            all_goals 
              omega
          ) he
          simpa using h
        have h4 : a ((4 + n) + 1) = 2 := by
          have h5 : a (4 + n) = 2 := ih (by omega)
          rw [h5] at h3
          omega
        rw [eq4']
        exact h4
      exact eq100
  have m : 100 = 4 + 96 := by norm_num
  rw [m] 
  apply h100 96 
  all_goals norm_num