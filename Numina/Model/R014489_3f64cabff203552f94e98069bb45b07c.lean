import Mathlib

theorem number_theory_19382 {b : ℕ} (hb : b > 1) :
    (Nat.ofDigits b [1, 1, 0, 1, 1]) * (b - 1) + (Nat.ofDigits b [1, 0, 0, 1]) =
    Nat.ofDigits b [0, 0, 1, 0, 0, 1] := by
  cases b with
  | zero =>
    linarith
  | succ b =>
    cases b with
    | zero =>
      linarith
    | succ b =>
      simp [Nat.ofDigits, mul_add, pow_two, pow_succ] at *
      <;> ring_nf
      <;> omega