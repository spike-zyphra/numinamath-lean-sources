import Mathlib

theorem number_theory_261780 (S : Finset ℤ) (hS : S = {-6, -4, -2, 0, 1, 3, 5, 7}) :
    IsGreatest {x | ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ x = a * b * c} 168 := by 
  constructor
  · -- Show 168 is in the set
    use -6, -4, 7
    simp [hS]
    all_goals omega
  · -- Show that there's no greater element in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, hne1, hne2, hne3, hx⟩
    -- expand the set membership
    simp [hS] at ha hb hc
    rcases ha with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> rcases hb with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> try { 
      omega
    } 
    <;> try { 
      tauto
    }
    <;> try { 
      nlinarith
      <;> omega
    }
    <;> try { 
      norm_num at hx ⊢
      <;> omega
    }
    <;> try { 
      norm_num at hx ⊢
      <;> omega
      <;> tauto
    }