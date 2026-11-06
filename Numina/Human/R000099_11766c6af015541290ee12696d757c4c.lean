import Mathlib

/- Show that if \( a, b, \) and \( c \) are integers, then the least common multiple of \( a \) and \( b \), denoted as \( [a, b] \), divides \( c \) if and only if both \( a \) divides \( c \) and \( b \) divides \( c \).-/
theorem number_theory_4583 (a b c : ℕ) : Nat.lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c :=by
  constructor
  -- **(1) Forward Direction: If \( [a, b] \mid c \), then \( a \mid c \) and \( b \mid c \)**
  intro h
  exact Nat.lcm_dvd_iff.mp h
  -- **(2) Reverse Direction: If \( a \mid c \) and \( b \mid c \), then \( [a, b] \mid c \)**
  intro h
  exact lcm_dvd_iff.mpr h