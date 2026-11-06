import Mathlib

def A : Set ℝ := {y | ∃ x : ℝ, y = x ^ 2 + 1}
def B : Set ℝ := {x | x ^ 2 + x - 2 > 0}

theorem algebra_10729 : A ∩ B = {y | y > 1} := by
  ext y 
  simp only [A, B, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First direction: if y ∈ A ∩ B, then y > 1
    rintro ⟨⟨x, hx⟩, h⟩
    nlinarith [sq_nonneg (x), sq_nonneg (y - 1)]
  · -- Second direction: if y > 1, then y ∈ A ∩ B 
    intro h
    constructor 
    · -- First part: prove y ∈ A
      use Real.sqrt (y - 1)
      have h2 : Real.sqrt (y - 1) ^ 2 = y - 1 := by 
        rw [Real.sq_sqrt]
        linarith
      nlinarith
    · -- Second part: prove y ∈ B
      nlinarith