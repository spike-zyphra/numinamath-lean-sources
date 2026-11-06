import Mathlib

open Nat

theorem number_theory_640373 {n p k: ℕ} (hp : Nat.Prime p) (hn : n > 0) (hk : k = ((p.digits n).sum))  :
  ∃ (E : ℕ), (E = (n - k) / (p - 1)) ∧ 
  (∃ m, (n ! / p ^ E) = m ∧ ¬m ≡ 0 [ZMOD p]) := by 
  use (padicValNat p n.factorial)
  have prime1 : Fact (Nat.Prime p) := by  
    exact { out := hp }
  -- use the Legendre formula `(p - 1) * padicValNat p n ! = n - (p.digits n).sum`.
  obtain h1 := @sub_one_mul_padicValNat_factorial p prime1 n
  rw [hk, ← h1, mul_comm]
  constructor
  · refine Eq.symm (mul_div_left (padicValNat p n !) ?_)
    have pge2 : p ≥ 2 := by 
      exact Prime.two_le hp
    omega
  use n ! / p ^ padicValNat p n !
  constructor
  rfl
  have notdvd : ¬ p ∣ (n ! / p ^ padicValNat p n !) := by 
    have aux1 : p ^ padicValNat p n ! ∣ n ! := by 
      exact pow_padicValNat_dvd
    obtain aux2 := padicValNat.div_pow aux1
    have aux3 : padicValNat p n ! - padicValNat p n ! = 0 := by 
      simp
    rw [aux3] at aux2
    by_contra hc
    have neq1 : n ! / p ^ padicValNat p n ! ≠ 0 := by 
      refine (div_ne_zero_iff_of_dvd aux1).mpr ?_
      constructor
      · exact factorial_ne_zero n
      · exact Ne.symm (NeZero.ne' (p ^ padicValNat p n !))
    obtain aux4 := (dvd_iff_padicValNat_ne_zero neq1).mp hc 
    exact aux4 aux2
  by_contra hc
  obtain aux := Int.ModEq.dvd (Int.ModEq.symm hc)
  simp at aux
  norm_cast at aux
