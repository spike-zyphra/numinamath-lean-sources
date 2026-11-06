import Mathlib

theorem number_theory_260028 (h : ∃ t : ℝ, t > 0 ∧ (t / 60) ^ 2 = t % 60) :
    t = 9.06 + 3 / 4 := by
  rcases h with ⟨t, ht_pos, heq⟩
  have h1 : t % 60 = t - (t / 60) * 60 := by
    field_simp [Nat.ofNat_pos]
    <;> ring
  rw [h1] at heq
  -- Since heq becomes (t/60).so^2 = 0, which implies t/60 = 0, hence t = 0
  have heq2 : (t / 60) ^ 2 = 0 := by 
    nlinarith
  have heq3 : (t / 60) = 0 := by 
    nlinarith
  have heq4 : t = 0 := by 
    linarith
  linarith