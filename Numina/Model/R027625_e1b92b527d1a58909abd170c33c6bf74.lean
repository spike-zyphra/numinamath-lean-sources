import Mathlib

theorem number_theory_179136 (p : ℕ) (hp : Nat.Prime p) :
    ¬ ∃ q : ℚ, q = Real.sqrt p := by
  rintro ⟨q, hq⟩
  have h1 : (q : ℝ) = Real.sqrt p := by
    simpa using hq
  have h4 : Irrational (Real.sqrt p) := by
    apply Nat.Prime.irrational_sqrt
    exact hp
  have h5 : ¬ Irrational (Real.sqrt p) := by
    rw [show Real.sqrt p = (q : ℝ) by linarith [h1]]
    simp
  contradiction