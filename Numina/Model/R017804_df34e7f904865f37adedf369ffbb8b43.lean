import Mathlib

theorem algebra_172803 {z : ℕ} (hz : z ∈ Finset.Icc 100 999) :
    (z - 5) * (z + 5) = z * z - 25 := by
  rw [Finset.mem_Icc] at hz
  rcases hz with ⟨hz1, hz2⟩
  have h3 : z ≥ 5 := by 
    omega -- z >= 100 so z >= 5
  cases z with
  | zero =>
    omega -- impossible
  | succ z =>
    cases z with
    | zero =>
      omega -- impossible
    | succ z =>
      cases z with
      | zero =>
        omega -- impossible
      | succ z =>
        cases z with
        | zero =>
          omega -- impossible
        | succ z =>
          cases z with
          | zero =>
            omega -- impossible
          | succ z => 
            simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.sub_add_cancel, Nat.add_sub_cancel, Nat.mul_sub, Nat.sub_mul] at *
            <;> ring_nf 
            <;> omega