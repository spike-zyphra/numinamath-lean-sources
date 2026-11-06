import Mathlib

/-- define solution as the set of Multiples of $d$ which less than or equal $x$ -/
def solution_4913 (d x : ℕ) : Set ℕ := {k | d ∣ k ∧ k ≤ x}

theorem number_theory_4913_a (d x : ℕ) (hd : d ≠ 0) : Nat.card (solution_4913 d x) = x / d + 1 := by
  -- the set of Multiples of $d$ which less than or equal $x$ is $\left \{0 * d, 1 * d, \cdots, x / d * d \right \}$. So it is equiv to `Fin (x / d + 1)`.
  have : solution_4913 d x ≃ Fin (x / d + 1) := {
    toFun := fun y => ⟨y.1 / d , by
      refine Nat.lt_add_one_of_le ?_
      refine Nat.div_le_div (y.2.2) (by simp) hd⟩
    invFun := fun n => ⟨ n * d, by
      simp [solution_4913]
      calc
        _ ≤ (x / d ) * d := Nat.mul_le_mul_right d (Nat.le_of_lt_add_one n.2)
        _ ≤ _ := Nat.div_mul_le_self x d⟩
    left_inv := by intro x ; simp [ ←Subtype.val_inj]; refine Nat.div_mul_cancel (x.2.1)
    right_inv := by intro x; simp [←Fin.val_inj]; exact Eq.symm (Nat.eq_div_of_mul_eq_left hd rfl)
  }
  simp [Nat.card_congr this ]

theorem number_theory_4913_b : Nat.card (solution_4913 5 1000) = 201 ∧ Nat.card (solution_4913 25 1000) = 41
  ∧ Nat.card (solution_4913 125 1000) = 9 ∧ Nat.card (solution_4913 625 1000) = 2:= by
  rw [number_theory_4913_a 5 1000 (by decide)]
  rw [number_theory_4913_a 25 1000 (by decide)]
  rw [number_theory_4913_a 125 1000 (by decide)]
  rw [number_theory_4913_a 625 1000 (by decide)]
  simp

theorem number_theory_4913_c : Nat.card (solution_4913 7 1000) = 143 ∧ Nat.card (solution_4913 7 100) = 15
  ∧ Nat.card (solution_4913 49 1000) = 21 ∧ Nat.card (solution_4913 49 100) = 3 := by
  rw [number_theory_4913_a 7 1000 (by decide)]
  rw [number_theory_4913_a 7 100 (by decide)]
  rw [number_theory_4913_a 49 1000 (by decide)]
  rw [number_theory_4913_a 49 100 (by decide)]
  simp