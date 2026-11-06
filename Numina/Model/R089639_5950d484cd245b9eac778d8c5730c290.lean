import Mathlib

theorem number_theory_111688 {P : ℕ} (hP : P = ∏ i ∈ Finset.Icc 1 100, Nat.factorial i) :
    ∃ k ∈ Finset.Icc 1 100, IsSquare (P / Nat.factorial k) := by

  use 50
  constructor
  · -- Show that 50 is in the interval from 1 to 100
    simp [Finset.mem_Icc]
  · -- Show that $P / 50!$ is a perfect square
    rw [hP]
    native_decide