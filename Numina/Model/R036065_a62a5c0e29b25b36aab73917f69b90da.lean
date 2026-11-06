import Mathlib

def is_twin_prime (a b : ℕ) : Prop := a.Prime ∧ b.Prime ∧ a < b ∧ a + 2 = b

theorem number_theory_3297 :
    IsGreatest {x | ∃ a b, x = a + b ∧ is_twin_prime a b ∧ a < 100} 144 := by
  constructor
  · -- Show that 144 is in the set, using a = 71 and b = 73
    use 71, 73
    all_goals
      norm_num [is_twin_prime]
      <;> try { native_decide }
  · -- Show that 144 is the greatest in the set
    intro x hx
    rcases hx with ⟨a, b, h1, h2, h3⟩
    rcases h2 with ⟨ha, hb, hab1, hab2⟩
    by_contra h
    push_neg at h
    have h4 : a + b > 144 := by 
      linarith
    have h5 : b = a + 2 := by
      omega
    rw [h5] at hb h4
    have h6 : a ≤ 99 := by
      omega
    interval_cases a <;> norm_num [h5] at ha hb h3 h4 ⊢
    <;> all_goals
      contradiction
      <;> try { native_decide }