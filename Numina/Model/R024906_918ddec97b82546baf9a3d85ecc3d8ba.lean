import Mathlib

def a : ℕ → ℕ
| 0 => 1
| n + 1 => if Even n then a n + 1 else 1

theorem number_theory_156287 : a 2020 = 1 := by
  have h1 : ∀ k : ℕ, a (2 * k) = 1 := by
    intro k
    induction k with
    | zero =>
      simp [a]
    | succ k ih =>
      have eq1 : a (2 * k + 1) = 2 := by
        simp [a, ih]
        <;> try { 
          have h3 : Even (2 * k) := by 
            simp [Nat.even_iff]
            <;> use k 
            <;> ring 
          simp [h3, if_pos]
          all_goals omega 
        }
        all_goals try { tauto }
      have eq2 : a (2 * (k + 1)) = 1 := by
        simp [a] at *
        all_goals ring_nf at *
        all_goals try { 
          have h3 : Even (2 * k) := by 
            simp [Nat.even_iff]
            <;> use k 
            <;> ring 
          simp [h3, if_pos] 
          all_goals try { 
            have h4 : ¬ Even (2 * k + 1) := by 
              intro h
              simp [Nat.even_iff] at h ⊢
              omega
            simp [h4, if_neg] 
            all_goals omega 
          } 
        }
        all_goals try { omega }
        all_goals try { tauto }
      exact eq2
  have h30 : a 2020 = 1 := by
    specialize h1 1010
    norm_num at h1 ⊢
    omega
  exact h30