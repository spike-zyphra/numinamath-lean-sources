import Mathlib

open Real

theorem algebra_116752 {G : Set ℝ} (hG : G = Set.Ioi 0) (n : ℕ) (hn : Odd n) (hn1 : n ≥ 3)
    (f : ℝ → ℝ) (hf : f = fun x => (logb 2 x)^n - 2^n) :
    (∀ x ∈ G, ∀ y ∈ G, x * y = y * x) ∧
    (∀ x ∈ G, ∃! y ∈ G, x * y = 4) := by
  constructor
  · -- Proof of the first part: multiplication is commutative 
    intros x hx y hy
    have hx' : x > 0 := by
      rw [hG] at hx
      simpa using hx
    have hy' : y > 0 := by
      rw [hG] at hy
      simpa using hy 
    ring_nf
  · -- Proof of the second part 
    intro x hx
    have hx1 : x > 0 := by 
      rw [hG] at hx
      simpa using hx 
    have hx2 : x ≠ 0 := by linarith 
    refine' ⟨4 / x, ⟨by
      rw [hG]
      simp only [Set.mem_Ioi]
      apply div_pos 
      all_goals linarith 
    , by 
      field_simp 
      <;> linarith 
    ⟩, _⟩ 
    intro y ⟨hy, heq⟩
    have hy1 : y > 0 := by
      rw [hG] at hy 
      simpa using hy 
    have h7 : y = 4 / x := by 
      field_simp at heq ⊢
      all_goals 
        linarith
    exact h7 
    all_goals linarith