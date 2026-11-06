import Mathlib

def A : Set ℕ := Finset.Icc 1 99
def B : Set ℕ := {x | ∃ n ∈ A, x = 2 * n}
def C : Set ℕ := {x | 2 * x ∈ A}

theorem number_theory_12603 : (B ∩ C).encard = 24 := by
  have h1 : B ∩ C = Finset.filter (fun x => (1 ≤ 2 * x ∧ 2 * x ≤ 99) ) (Finset.image (fun n => 2 * n) (Finset.Icc 1 99)) := by
    ext x
    simp [B, C, A]
    aesop
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide