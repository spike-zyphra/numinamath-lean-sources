import Mathlib

def is_sextalternado (n : ℕ) : Prop :=
  (Nat.digits 10 n).length = 8 ∧ 30 ∣ n ∧ ∀ i, Even ((Nat.digits 10 n)[i]!) ≠ Odd ((Nat.digits 10 n)[i + 1]!)

def is_super_sextalternado (n : ℕ) : Prop :=
  is_sextalternado n ∧ 12 ∣ n

theorem number_theory_52669 :
    ¬∃ n, is_super_sextalternado n ∧
    IsLeast {n | is_sextalternado n} 10101030 := by
  rintro ⟨n, hn, h1⟩
  have h2 : is_sextalternado 10101030 := by
    exact h1.left
  rcases h2 with ⟨h_length, h_30, h_parity⟩
  have h3 := h_parity 0
  norm_num at h3
  all_goals contradiction